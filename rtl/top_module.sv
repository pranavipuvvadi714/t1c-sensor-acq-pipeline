module neural_acq_top #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4,
    parameter NUM_CHANNELS = 16
) (
    // Clock Domain 1: Sensor (Slow, e.g., 32kHz)
    input  logic                     sensor_clk,
    input  logic                     sensor_rst_n,
    // New Interface: Parallel inputs from 16 ADCs
    input  logic [DATA_WIDTH-1:0]    sensor_data_in [NUM_CHANNELS],
    input  logic                     sensor_valid_all,

    // Clock Domain 2: System (Fast, e.g., 1MHz)
    input  logic                     sys_clk,
    input  logic                     sys_rst_n,

    // Clock Domain 3: Output Interface (Variable, e.g., SPI rate)
    input  logic                     out_clk,
    input  logic                     out_rst_n,
    output logic [63:0]              dout,
    output logic                     dout_valid,
    input  logic                     dout_ready,

    // CSR Interface (System Domain)
    input  logic [2:0]               csr_addr,
    input  logic                     csr_write,
    input  logic [31:0]              csr_wdata,
    output logic [31:0]              csr_rdata
);

    // --- Interconnect Signals (SYS_CLK Domain) ---
    logic [DATA_WIDTH-1:0]    agg_data;
    logic [CH_ID_WIDTH-1:0]   agg_channel;
    logic                     agg_valid;

    logic [DATA_WIDTH-1:0]    fe_data;
    logic [CH_ID_WIDTH-1:0]   fe_channel;
    logic                     fe_valid;

    logic [63:0]              framer_packet;
    logic                     framer_valid;

    logic                     fifo_full;
    logic                     fifo_empty; // Note: This is in OUT_CLK domain!
    logic                     fifo_rd_en;

    // CSR Signals
    logic                     reg_enable;
    logic                     reg_overflow_sticky;
    
    // Status Synchronization (out_clk -> sys_clk)
    logic                     fifo_empty_sync1, fifo_empty_sync2;

    // -------------------------------------------------------------
    // 1. Module Instantiations
    // -------------------------------------------------------------

    // A. Aggregator (Bridges SENSOR_CLK -> SYS_CLK)
    neural_aggregator #(
        .NUM_CHANNELS(NUM_CHANNELS), .DATA_WIDTH(DATA_WIDTH), .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_aggregator (
        .sensor_clk       (sensor_clk),
        .sys_clk          (sys_clk), // Sweep runs on Fast Clock
        .rst_n            (sensor_rst_n), // Reset usually follows sensor power domain or system
        .sensor_data_in   (sensor_data_in),
        .sensor_valid_all (sensor_valid_all),
        .adc_data_out     (agg_data),
        .adc_channel_out  (agg_channel),
        .adc_valid_out    (agg_valid)
    );

    // B. Frontend (Processing on SYS_CLK)
    // Note: We connect sys_clk to the 'sensor_clk' port of the submodule
    neural_acq_frontend #(
        .DATA_WIDTH(DATA_WIDTH), .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_frontend (
        .sensor_clk     (sys_clk),      // REMAPPED to SYS_CLK
        .sensor_rst_n   (sys_rst_n),
        .adc_data_in    (agg_data),
        .adc_channel_in (agg_channel),
        .adc_valid_in   (agg_valid),
        .ch_enable      (reg_enable),   // Direct connection (same domain)
        .acq_data       (fe_data),
        .acq_channel    (fe_channel),
        .acq_valid      (fe_valid)
    );

    // C. Framer (Packetizing on SYS_CLK)
    neural_packet_framer #(
        .DATA_WIDTH(DATA_WIDTH), .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_framer (
        .sensor_clk     (sys_clk),      // REMAPPED to SYS_CLK
        .sensor_rst_n   (sys_rst_n),
        .acq_data       (fe_data),
        .acq_channel    (fe_channel),
        .acq_valid      (fe_valid),
        .framed_packet  (framer_packet),
        .framed_valid   (framer_valid)
    );

    // D. Async FIFO (Bridges SYS_CLK -> OUT_CLK)
    wire fifo_wr_en = framer_valid && !fifo_full;

    async_fifo #(
        .DATA_WIDTH(64), .DEPTH_LOG2(5) 
    ) u_fifo (
        // Write Side (System Domain)
        .wr_clk   (sys_clk),
        .wr_rst_n (sys_rst_n),
        .wr_en    (fifo_wr_en),
        .wr_data  (framer_packet),
        .full     (fifo_full),

        // Read Side (Output Domain)
        .rd_clk   (out_clk),
        .rd_rst_n (out_rst_n),
        .rd_en    (fifo_rd_en),
        .rd_data  (dout),
        .empty    (fifo_empty)
    );

    // Output Handshake (OUT_CLK Domain)
    assign dout_valid = !fifo_empty;
    assign fifo_rd_en = dout_ready && !fifo_empty;

    // -------------------------------------------------------------
    // 2. CSR Logic (SYS_CLK Domain)
    // -------------------------------------------------------------
    
    // Synchronize 'fifo_empty' (from out_clk) to sys_clk for status register
    always_ff @(posedge sys_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) {fifo_empty_sync2, fifo_empty_sync1} <= 2'b11; // Reset to empty
        else            {fifo_empty_sync2, fifo_empty_sync1} <= {fifo_empty_sync1, fifo_empty};
    end

    // CSR Read/Write
    always_ff @(posedge sys_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            reg_enable <= 1'b0;
            reg_overflow_sticky <= 1'b0;
        end else begin
            // Write
            if (csr_write && csr_addr == 3'h0) 
                reg_enable <= csr_wdata[0];
            
            // Sticky Error (accumulate)
            if (fifo_full && framer_valid) 
                reg_overflow_sticky <= 1'b1;
        end
    end

    // Read
    always_comb begin
        case (csr_addr)
            3'h0: csr_rdata = {31'b0, reg_enable};
            // Return synced empty flag to prevent metastability on bus
            3'h1: csr_rdata = {29'b0, reg_overflow_sticky, fifo_full, fifo_empty_sync2};
            default: csr_rdata = 32'b0;
        endcase
    end

endmodule