module neural_aggregator #(
    parameter NUM_CHANNELS = 16,
    parameter DATA_WIDTH   = 16,
    parameter CH_ID_WIDTH  = 4
) (
    // Clocking
    input  logic                     sensor_clk,   // Slow clock (Capture)
    input  logic                     sys_clk,      // Fast clock (Sweep)
    input  logic                     rst_n,

    // Interface from 16 Sensors (sensor_clk domain)
    input  logic [DATA_WIDTH-1:0]    sensor_data_in [NUM_CHANNELS],
    input  logic                     sensor_valid_all, 

    // Interface to neural_acq_frontend (sys_clk domain)
    output logic [DATA_WIDTH-1:0]    adc_data_out,
    output logic [CH_ID_WIDTH-1:0]   adc_channel_out,
    output logic                     adc_valid_out
);

    // FIXED: Removed [NUM_CHANNELS-1:0] to match input array direction [0:15]
    // This prevents the channel reversal bug.
    logic [DATA_WIDTH-1:0] shadow_regs [NUM_CHANNELS];
    
    always_ff @(posedge sensor_clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_CHANNELS; i++) shadow_regs[i] <= '0;
        end else if (sensor_valid_all) begin
            shadow_regs <= sensor_data_in; 
        end
    end

    // CDC Synchronization (sensor_clk -> sys_clk)
    logic sync_req_q1, sync_req_q2, sync_req_q3;
    logic start_sweep_pulse;
    
    always_ff @(posedge sys_clk or negedge rst_n) begin
        if (!rst_n) begin
            sync_req_q1 <= 1'b0;
            sync_req_q2 <= 1'b0;
            sync_req_q3 <= 1'b0;
        end else begin
            sync_req_q1 <= sensor_valid_all;
            sync_req_q2 <= sync_req_q1;
            sync_req_q3 <= sync_req_q2;
        end
    end

    // Rising Edge Detector
    assign start_sweep_pulse = sync_req_q2 && !sync_req_q3;

    // TDM Sweep Logic (sys_clk domain)
    logic [CH_ID_WIDTH-1:0] rr_ptr;
    logic                   is_sweeping;

    always_ff @(posedge sys_clk or negedge rst_n) begin
        if (!rst_n) begin
            rr_ptr          <= '0;
            is_sweeping     <= 1'b0;
            adc_valid_out   <= 1'b0;
            adc_data_out    <= '0;
            adc_channel_out <= '0;
        end else begin
            if (start_sweep_pulse && !is_sweeping) begin
                is_sweeping <= 1'b1;
                rr_ptr      <= '0;
            end 
            
            if (is_sweeping) begin
                adc_data_out    <= shadow_regs[rr_ptr];
                adc_channel_out <= rr_ptr;
                adc_valid_out   <= 1'b1;

                if (rr_ptr == (NUM_CHANNELS-1)) begin
                    is_sweeping <= 1'b0;
                end else begin
                    rr_ptr <= rr_ptr + 1'b1;
                end
            end else begin
                adc_valid_out <= 1'b0;
            end
        end
    end
endmodule
