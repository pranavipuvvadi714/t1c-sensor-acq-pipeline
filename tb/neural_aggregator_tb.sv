`timescale 1ns/1ps

module neural_aggregator_tb;

    parameter NUM_CHANNELS = 16;
    parameter DATA_WIDTH   = 16;
    parameter CH_ID_WIDTH  = 4;

    logic                    sensor_clk = 0;
    logic                    sys_clk    = 0;
    logic                    rst_n;
    logic [NUM_CHANNELS-1:0] channel_mask;
    logic [DATA_WIDTH-1:0]   sensor_data_in [NUM_CHANNELS];
    logic                    sensor_valid_all;

    logic [DATA_WIDTH-1:0]   adc_data_out;
    logic [CH_ID_WIDTH-1:0]  adc_channel_out;
    logic                    adc_valid_out;

    // --- Scoreboard / Truth Storage ---
    logic [DATA_WIDTH-1:0]   shadow_truth [NUM_CHANNELS];
    int log_file;
    int error_count = 0;
    int match_count = 0;

    // Clock Generation
    always #50 sensor_clk = ~sensor_clk; 
    always #5  sys_clk    = ~sys_clk;    

    neural_aggregator #(16, 16, 4) dut (.*);

    // --- Main Stimulus Block ---
    initial begin
        log_file = $fopen("simulation_log.txt", "w");
        $fdisplay(log_file, "--- Starting Aggregator Test (Synchronized) ---");
        
        // 1. System Reset
        rst_n = 0;
        sensor_valid_all = 0;
        channel_mask = '0;
        for (int i=0; i<NUM_CHANNELS; i++) sensor_data_in[i] = '0;
        #200 rst_n = 1;
        
        // Wait for CDC sync logic to settle
        repeat (10) @(posedge sys_clk);

        for (int iter = 0; iter < 20; iter++) begin
            automatic logic [NUM_CHANNELS-1:0] current_mask = $urandom();
            
            // 2. Drive Sensor Data
            @(posedge sensor_clk);
            channel_mask     <= current_mask;
            sensor_valid_all <= 1'b1;
            
            for (int i=0; i<NUM_CHANNELS; i++) begin
                automatic logic [DATA_WIDTH-1:0] val = $urandom() & 16'hFFFF;
                sensor_data_in[i] <= val;
                // Update Truth immediately so checker is ready for the upcoming sweep
                shadow_truth[i]   <= val; 
            end

            $display("T=%0t | Iter %0d | Mask: %h", $time, iter, current_mask);
            $fdisplay(log_file, "\n--- Iteration %0d | Mask: %b ---", iter, current_mask);

            @(posedge sensor_clk);
            sensor_valid_all <= 1'b0;

            // 3. CRITICAL: Wait for the sweep to be TOTALLY finished
            // before starting the next iteration to prevent overlap.
            // 16 channels * 10 sys_clks per sensor_clk = plenty of time.
            repeat (60) @(posedge sys_clk); 
        end

        $display("\nSimulation Finished. Total Matches: %0d, Errors: %0d", match_count, error_count);
        $fdisplay(log_file, "\nFinal Results -> Matches: %0d, Errors: %0d", match_count, error_count);
        $fclose(log_file);
        $finish;
    end

    // --- Checker Logic (Scoreboard) ---
    always @(posedge sys_clk) begin
        if (adc_valid_out) begin
            // Verify data against our shadow copy
            if (adc_data_out !== shadow_truth[adc_channel_out]) begin
                $fdisplay(log_file, "T=%0t | [FAIL] CH %0d | Exp: %h | Got: %h", 
                          $time, adc_channel_out, shadow_truth[adc_channel_out], adc_data_out);
                error_count++;
            end else begin
                $fdisplay(log_file, "T=%0t | [PASS] CH %0d | Data: %h", 
                          $time, adc_channel_out, adc_data_out);
                match_count++;
            end
        end
    end

endmodule