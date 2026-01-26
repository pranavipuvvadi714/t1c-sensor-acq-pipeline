module neural_acq_top #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4,
    parameter NUM_CHANNELS = 16
) (
    input  logic                     sensor_clk,
    input  logic                     sensor_rst_n,

    input  logic [DATA_WIDTH-1:0]    sensor_data_in [NUM_CHANNELS],
    input  logic                     sensor_valid_all,

    input  logic                     sys_clk,
    input  logic                     sys_rst_n,

    input  logic                     out_clk,
    input  logic                     out_rst_n,
    output logic [63:0]              dout,
    output logic                     dout_valid,
    input  logic                     dout_ready,

    input  logic [2:0]               csr_addr,
    input  logic                     csr_write,
    input  logic [31:0]              csr_wdata,
    output logic [31:0]              csr_rdata
);

    logic [DATA_WIDTH-1:0]    agg_data;
    logic [CH_ID_WIDTH-1:0]   agg_channel;
    logic                     agg_valid;

    logic [DATA_WIDTH-1:0]    fe_data;
    logic [CH_ID_WIDTH-1:0]   fe_channel;
    logic                     fe_valid;

    logic [63:0]              framer_packet;
    logic                     framer_valid;

    logic                     fifo_full;
    logic                     fifo_empty;
    logic                     fifo_rd_en;

    logic                     reg_global_enable;   
    logic                     reg_overflow_sticky;
    logic [NUM_CHANNELS-1:0]  reg_channel_mask;    

    logic                     fifo_empty_sync1, fifo_empty_sync2;

    neural_aggregator #(
        .NUM_CHANNELS(NUM_CHANNELS), 
        .DATA_WIDTH(DATA_WIDTH), 
        .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_aggregator (
        .sensor_clk       (sensor_clk),
        .sys_clk          (sys_clk), 
        .rst_n            (sensor_rst_n),
        
        .channel_mask     (reg_channel_mask), 

        .sensor_data_in   (sensor_data_in),
        .sensor_valid_all (sensor_valid_all),
        .adc_data_out     (agg_data),
        .adc_channel_out  (agg_channel),
        .adc_valid_out    (agg_valid)
    );

    neural_acq_frontend #(
        .DATA_WIDTH(DATA_WIDTH), 
        .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_frontend (
        .sensor_clk       (sys_clk),      
        .sensor_rst_n     (sys_rst_n),
        .adc_data_in      (agg_data),
        .adc_channel_in   (agg_channel),
        .adc_valid_in     (agg_valid),
        .acq_data         (fe_data),
        .acq_channel      (fe_channel),
        .acq_valid        (fe_valid)
    );

    neural_packet_framer #(
        .DATA_WIDTH(DATA_WIDTH), 
        .CH_ID_WIDTH(CH_ID_WIDTH)
    ) u_framer (
        .sensor_clk       (sys_clk),      
        .sensor_rst_n     (sys_rst_n),
        .acq_data         (fe_data),
        .acq_channel      (fe_channel),
        .acq_valid        (fe_valid),
        .framed_packet    (framer_packet),
        .framed_valid     (framer_valid)
    );

    wire fifo_wr_en = framer_valid && !fifo_full;

    async_fifo #(
        .DATA_WIDTH(64), 
        .DEPTH_LOG2(5) 
    ) u_fifo (

        .wr_clk   (sys_clk),
        .wr_rst_n (sys_rst_n),
        .wr_en    (fifo_wr_en),
        .wr_data  (framer_packet),
        .full     (fifo_full),

        .rd_clk   (out_clk),
        .rd_rst_n (out_rst_n),
        .rd_en    (fifo_rd_en),
        .rd_data  (dout),
        .empty    (fifo_empty)
    );

    assign dout_valid = !fifo_empty;
    assign fifo_rd_en = dout_ready && !fifo_empty;

    always_ff @(posedge sys_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) {fifo_empty_sync2, fifo_empty_sync1} <= 2'b11;
        else            {fifo_empty_sync2, fifo_empty_sync1} <= {fifo_empty_sync1, fifo_empty};
    end

    always_ff @(posedge sys_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            reg_global_enable   <= 1'b0;
            reg_overflow_sticky <= 1'b0;
            reg_channel_mask    <= 16'hFFFF; //default all channels are enabled
        end else begin
           
            if (csr_write) begin
                case (csr_addr)
                    3'h0: reg_global_enable <= csr_wdata[0];
                    3'h2: reg_channel_mask  <= csr_wdata[15:0]; // Write Mask
                endcase
            end
     
            if (fifo_full && framer_valid) 
                reg_overflow_sticky <= 1'b1;
        end
    end

    always_comb begin
        case (csr_addr)
            3'h0: csr_rdata = {31'b0, reg_global_enable};
            3'h1: csr_rdata = {29'b0, reg_overflow_sticky, fifo_full, fifo_empty_sync2};
            3'h2: csr_rdata = {16'b0, reg_channel_mask};
            default: csr_rdata = 32'b0;
        endcase
    end

endmodule
