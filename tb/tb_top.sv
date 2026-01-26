/*`timescale 1ns / 1ps

module tb_neural_acq_top;

    // -------------------------------------------------------------------------
    // 1. Parameters & Signals
    // -------------------------------------------------------------------------
    parameter DATA_WIDTH   = 16;
    parameter CH_ID_WIDTH  = 4;
    parameter NUM_CHANNELS = 16;

    // Clock and Reset
    logic sensor_clk, sensor_rst_n;
    logic sys_clk, sys_rst_n;
    logic out_clk, out_rst_n;

    // Sensor Interface (Parallel Input Array)
    logic [DATA_WIDTH-1:0] sensor_data_in [NUM_CHANNELS];
    logic                  sensor_valid_all;

    // System Bus Interface (Output Domain)
    logic [63:0]           dout;
    logic                  dout_valid;
    logic                  dout_ready;

    // CSR Interface (System Domain)
    logic [2:0]            csr_addr;
    logic                  csr_write;
    logic [31:0]           csr_wdata;
    logic [31:0]           csr_rdata;

    // Simulation Control
    int error_count = 0;
    int transaction_count = 0;
    localparam TEST_LOOPS = 5;
    
    // Shadow register to track if DUT is enabled (for scoreboard logic)
    logic tb_enabled_shadow = 0; 

    // -------------------------------------------------------------------------
    // 2. Clock Generation
    // -------------------------------------------------------------------------
    // Sensor Clock: 1 MHz
    initial begin
        sensor_clk = 0;
        forever #500 sensor_clk = ~sensor_clk; 
    end

    // System Clock: 50 MHz
    initial begin
        sys_clk = 0;
        forever #10 sys_clk = ~sys_clk;
    end

    // Output Clock: 25 MHz
    initial begin
        out_clk = 0;
        forever #20 out_clk = ~out_clk;
    end

    // -------------------------------------------------------------------------
    // 3. DUT Instantiation
    // -------------------------------------------------------------------------
    neural_acq_top #(
        .DATA_WIDTH(DATA_WIDTH),
        .CH_ID_WIDTH(CH_ID_WIDTH),
        .NUM_CHANNELS(NUM_CHANNELS)
    ) dut (
        // Sensor Domain
        .sensor_clk       (sensor_clk),
        .sensor_rst_n     (sensor_rst_n),
        .sensor_data_in   (sensor_data_in),
        .sensor_valid_all (sensor_valid_all),

        // System Domain
        .sys_clk          (sys_clk),
        .sys_rst_n        (sys_rst_n),

        // Output Domain
        .out_clk          (out_clk),
        .out_rst_n        (out_rst_n),
        .dout             (dout),
        .dout_valid       (dout_valid),
        .dout_ready       (dout_ready),

        // CSR
        .csr_addr         (csr_addr),
        .csr_write        (csr_write),
        .csr_wdata        (csr_wdata),
        .csr_rdata        (csr_rdata)
    );

    // -------------------------------------------------------------------------
    // 4. Verification Structures (Scoreboard)
    // -------------------------------------------------------------------------
    typedef struct {
        logic [DATA_WIDTH-1:0]  data;
        logic [CH_ID_WIDTH-1:0] ch;
    } expected_packet_t;

    expected_packet_t scoreboard_q[$];

    // -------------------------------------------------------------------------
    // 5. Tasks
    // -------------------------------------------------------------------------

    task apply_reset();
        $display("[%0t] Asserting Resets...", $time);
        sensor_rst_n = 0;
        sys_rst_n    = 0;
        out_rst_n    = 0;
        
        sensor_valid_all = 0;
        for(int i=0; i<NUM_CHANNELS; i++) sensor_data_in[i] = '0;
        
        csr_write  = 0;
        dout_ready = 1; // Default: Receiver always ready
        
        repeat(10) @(posedge sys_clk);
        sys_rst_n = 1;
        out_rst_n = 1;
        
        // Hold sensor reset longer to ensure proper startup
        repeat(20) @(posedge sensor_clk);
        sensor_rst_n = 1;
        
        $display("[%0t] Resets Deasserted.", $time);
    endtask

    task csr_write_reg(input logic [2:0] addr, input logic [31:0] data);
        @(posedge sys_clk);
        csr_addr  <= addr;
        csr_wdata <= data;
        csr_write <= 1;
        // Update shadow logic immediately to match DUT behavior (ideal)
        if (addr == 3'h0) tb_enabled_shadow = data[0]; 
        @(posedge sys_clk);
        csr_write <= 0;
        $display("[%0t] CSR Write: Addr 0x%h, Data 0x%h", $time, addr, data);
    endtask

    // Generates a parallel capture event across all 16 channels
    // Uses 'automatic' to ensure fresh variable allocation per call
    task automatic trigger_sensor_capture();
        logic [DATA_WIDTH-1:0] data_snapshot [NUM_CHANNELS];

        // 1. Prepare Data snapshot
        for (int i=0; i < NUM_CHANNELS; i++) begin
            data_snapshot[i] = $urandom();
        end

        // 2. Scoreboard Prediction (Push BEFORE driving)
        if (tb_enabled_shadow) begin
            $display("[%0t] Sensors Triggered (Enabled). Expecting 16 packets.", $time);
            for (int i=0; i < NUM_CHANNELS; i++) begin
                expected_packet_t pkt;
                pkt.ch   = i[3:0];
                pkt.data = data_snapshot[i];
                scoreboard_q.push_back(pkt);
            end
        end else begin
            $display("[%0t] Sensors Triggered (Disabled). Expecting data drop.", $time);
        end

        // 3. Drive Signals on POSEDGE with Delay (Avoids race conditions)
        @(posedge sensor_clk);
        #1; 
        for (int i=0; i < NUM_CHANNELS; i++) begin
            sensor_data_in[i] = data_snapshot[i];
        end
        sensor_valid_all = 1;

        // 4. Hold for one full clock cycle
        @(posedge sensor_clk);
        #1;
        sensor_valid_all = 0;
    endtask

    // -------------------------------------------------------------------------
    // 6. Monitor Process (Consumer on Output Domain)
    // -------------------------------------------------------------------------
    initial begin
        expected_packet_t exp_pkt;
        logic [31:0] received_ts;
        logic [CH_ID_WIDTH-1:0] received_ch;
        logic [DATA_WIDTH-1:0] received_data;

        forever begin
            // Monitor must watch the OUTPUT clock domain
            @(posedge out_clk); 
            
            if (dout_valid && dout_ready) begin
                // Decode the 64-bit Packet
                // [63:32] TS, [31:28] CH, [27:12] DATA, [11:0] RSV
                received_ts   = dout[63:32];
                received_ch   = dout[31:28];
                received_data = dout[27:12];

                //$display("[%0t] Monitor: Received Packet CH=%h Data=%h", $time, received_ch, received_data);

                if (scoreboard_q.size() == 0) begin
                    $error("[%0t] ERROR: Unexpected data! Q empty. CH=%h Data=%h", 
                           $time, received_ch, received_data);
                    error_count++;
                end else begin
                    exp_pkt = scoreboard_q.pop_front();
                    
                    if (received_data !== exp_pkt.data || received_ch !== exp_pkt.ch) begin
                        $error("[%0t] MISMATCH! Exp: {CH=%h, Data=%h}, Got: {CH=%h, Data=%h}", 
                               $time, exp_pkt.ch, exp_pkt.data, received_ch, received_data);
                        error_count++;
                    end else begin
                        transaction_count++;
                    end
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // 7. Stimulus
    // -------------------------------------------------------------------------
    initial begin
        apply_reset();

        // -------------------------------------------------
        // Test 1: Trigger while Disabled (Default)
        // -------------------------------------------------
        $display("\n--- Test 1: Disabled Capture ---");
        trigger_sensor_capture(); 
        
        repeat(100) @(posedge sys_clk); // Wait to ensure no leakage
        if (transaction_count > 0) begin
            $error("Data leaked while disabled!");
            error_count++;
        end

        // -------------------------------------------------
        // Test 2: Enable and Capture
        // -------------------------------------------------
        $display("\n--- Test 2: Enabled Capture ---");
        csr_write_reg(3'h0, 32'h1); // Enable bit = 1
        
        // Wait for CDC sync of enable signal
        repeat(20) @(posedge sensor_clk);

        for (int i=0; i<TEST_LOOPS; i++) begin
            trigger_sensor_capture();
            
            // Wait for sweep to finish (16 channels) + FIFO drain
            // Sweep = 16 * 20ns = 320ns
            // Drain = 16 * 40ns = 640ns
            // Wait > 1000ns
            repeat(500) @(posedge sys_clk); 
        end

        // -------------------------------------------------
        // Test 3: Drain Check
        // -------------------------------------------------
        $display("\n--- Test 3: Draining ---");
        // Wait for scoreboard to empty
        fork
            wait(scoreboard_q.size() == 0);
            begin
                // Increase timeout to 20,000 cycles (400us)
                repeat(20000) @(posedge sys_clk);
                $error("Timeout waiting for scoreboard to drain! Pending: %0d", scoreboard_q.size());
                error_count++;
            end
        join_any

        // -------------------------------------------------
        // Final Status
        // -------------------------------------------------
        if (error_count == 0 && transaction_count == (TEST_LOOPS * 16)) begin
            $display("\nSUCCESS: All %0d packets verified.", transaction_count);
        end else begin
            $display("\nFAILURE: Errors=%0d, Trans=%0d (Exp %0d)", 
                     error_count, transaction_count, TEST_LOOPS*16);
        end
        $finish;
    end

endmodule */

`timescale 1ns / 1ps

module tb_simple_neural;

    // -------------------------------------------------------------------------
    // 1. Signals & Parameters
    // -------------------------------------------------------------------------
    parameter DATA_WIDTH   = 16;
    parameter CH_ID_WIDTH  = 4;
    parameter NUM_CHANNELS = 16;

    // Clocks and Resets
    logic sensor_clk, sensor_rst_n;
    logic sys_clk, sys_rst_n;
    logic out_clk, out_rst_n;

    // Inputs
    logic [DATA_WIDTH-1:0] sensor_data_in [NUM_CHANNELS];
    logic                  sensor_valid_all;
    
    // Outputs
    logic [63:0]           dout;
    logic                  dout_valid;
    logic                  dout_ready;

    // CSR (Control Status Register)
    logic [2:0]            csr_addr;
    logic                  csr_write;
    logic [31:0]           csr_wdata;
    logic [31:0]           csr_rdata;

    // -------------------------------------------------------------------------
    // 2. Clock Generation
    // -------------------------------------------------------------------------
    initial begin
        sensor_clk = 0;
        forever #500 sensor_clk = ~sensor_clk; // 1 MHz
    end

    initial begin
        sys_clk = 0;
        forever #10 sys_clk = ~sys_clk;        // 50 MHz
    end

    initial begin
        out_clk = 0;
        forever #20 out_clk = ~out_clk;        // 25 MHz
    end

    // -------------------------------------------------------------------------
    // 3. DUT Instantiation
    // -------------------------------------------------------------------------
    neural_acq_top #(
        .DATA_WIDTH(DATA_WIDTH),
        .CH_ID_WIDTH(CH_ID_WIDTH),
        .NUM_CHANNELS(NUM_CHANNELS)
    ) dut (
        .sensor_clk       (sensor_clk),
        .sensor_rst_n     (sensor_rst_n),
        .sensor_data_in   (sensor_data_in),
        .sensor_valid_all (sensor_valid_all),

        .sys_clk          (sys_clk),
        .sys_rst_n        (sys_rst_n),

        .out_clk          (out_clk),
        .out_rst_n        (out_rst_n),
        .dout             (dout),
        .dout_valid       (dout_valid),
        .dout_ready       (dout_ready),

        .csr_addr         (csr_addr),
        .csr_write        (csr_write),
        .csr_wdata        (csr_wdata),
        .csr_rdata        (csr_rdata)
    );

    // -------------------------------------------------------------------------
    // 4. Output Monitor (Just print what we see)
    // -------------------------------------------------------------------------
    always @(posedge out_clk) begin
        if (dout_valid && dout_ready) begin
            $display("[%0t ns] OUTPUT RECEIVED: Channel=%0d, Data=0x%h, Timestamp=%0d", 
                     $time, dout[31:28], dout[27:12], dout[63:32]);
        end
    end

    // -------------------------------------------------------------------------
    // 5. Main Stimulus
    // -------------------------------------------------------------------------
    initial begin
        // Initialize Inputs
        sensor_valid_all = 0;
        for (int i = 0; i < NUM_CHANNELS; i++) sensor_data_in[i] = 0;
        dout_ready = 1; // Always ready to receive
        csr_write = 0;

        // --- RESET SEQUENCE ---
        $display("Applying Reset...");
        sensor_rst_n = 0; sys_rst_n = 0; out_rst_n = 0;
        repeat(20) @(posedge sys_clk);
        sys_rst_n = 1; out_rst_n = 1;
        repeat(20) @(posedge sensor_clk);
        sensor_rst_n = 1;
        $display("Reset Complete.");

        // --- STEP 1: ENABLE THE SYSTEM (CSR) ---
        // If we don't do this, the frontend will gate (block) all data.
        @(posedge sys_clk);
        csr_addr  <= 3'h0;      // Control Register Address
        csr_wdata <= 32'h1;     // Bit 0 = Enable
        csr_write <= 1;
        @(posedge sys_clk);
        csr_write <= 0;
        $display("System Enabled via CSR.");

        // Wait for enable signal to cross clock domains
        repeat(10) @(posedge sensor_clk);

        // --- STEP 2: SEND DATA BURST 1 ---
        $display("Sending Burst 1 (Fixed Pattern: Data = Channel ID * 0x100)...");
        
        // Setup data on the bus (synchronous to sensor clock)
        @(posedge sensor_clk);
        #1; // Slight delay after edge
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            sensor_data_in[i] = i * 16'h0100; // Ch0=0x0000, Ch1=0x0100, Ch2=0x0200...
        end
        sensor_valid_all = 1;

        // Hold valid for 1 clock cycle
        @(posedge sensor_clk);
        #1;
        sensor_valid_all = 0;

        // Wait for processing
        repeat(200) @(posedge sys_clk);

        // --- STEP 3: SEND DATA BURST 2 ---
        $display("Sending Burst 2 (Fixed Pattern: Data = 0xAAAA)...");
        
        @(posedge sensor_clk);
        #1;
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            sensor_data_in[i] = 16'hAAAA;
        end
        sensor_valid_all = 1;

        @(posedge sensor_clk);
        #1;
        sensor_valid_all = 0;

        // Wait for processing
        repeat(500) @(posedge sys_clk);

        $display("Test Complete.");
        $finish;
    end

endmodule
