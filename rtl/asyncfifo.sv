module async_fifo #(
    parameter DATA_WIDTH = 64,
    parameter DEPTH_LOG2 = 4
) (
    input  logic                    wr_clk,
    input  logic                    wr_rst_n,
    input  logic                    wr_en,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    full,

    input  logic                    rd_clk,
    input  logic                    rd_rst_n,
    input  logic                    rd_en,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    empty
);
    localparam DEPTH = 1 << DEPTH_LOG2;
    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
    logic [DEPTH_LOG2:0] wr_ptr_bin, wr_ptr_gray;
    logic [DEPTH_LOG2:0] rd_ptr_bin, rd_ptr_gray;
    logic [DEPTH_LOG2:0] wr_ptr_gray_sync1, wr_ptr_gray_sync2;
    logic [DEPTH_LOG2:0] rd_ptr_gray_sync1, rd_ptr_gray_sync2;

    // Write Domain
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_ptr_bin  <= '0;
            wr_ptr_gray <= '0;
        end else if (wr_en && !full) begin
            mem[wr_ptr_bin[DEPTH_LOG2-1:0]] <= wr_data;
            wr_ptr_bin  <= wr_ptr_bin + 1;
            wr_ptr_gray <= (wr_ptr_bin + 1) ^ ((wr_ptr_bin + 1) >> 1);
        end
    end

    // Read Domain
    assign rd_data = mem[rd_ptr_bin[DEPTH_LOG2-1:0]];
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            rd_ptr_bin  <= '0;
            rd_ptr_gray <= '0;
        end else if (rd_en && !empty) begin
            rd_ptr_bin  <= rd_ptr_bin + 1;
            rd_ptr_gray <= (rd_ptr_bin + 1) ^ ((rd_ptr_bin + 1) >> 1);
        end
    end

    // Synchronizers
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) {rd_ptr_gray_sync2, rd_ptr_gray_sync1} <= '0;
        else           {rd_ptr_gray_sync2, rd_ptr_gray_sync1} <= {rd_ptr_gray_sync1, rd_ptr_gray};
    end
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) {wr_ptr_gray_sync2, wr_ptr_gray_sync1} <= '0;
        else           {wr_ptr_gray_sync2, wr_ptr_gray_sync1} <= {wr_ptr_gray_sync1, wr_ptr_gray};
    end

    assign full = (wr_ptr_gray == {~rd_ptr_gray_sync2[DEPTH_LOG2:DEPTH_LOG2-1], rd_ptr_gray_sync2[DEPTH_LOG2-2:0]});
    assign empty = (rd_ptr_gray == wr_ptr_gray_sync2);

assert_no_overflow: assert property (@(posedge wr_clk) disable iff (!wr_rst_n)
        wr_en |-> !full)
        else $error("Error: FIFO Overflow! Write attempted while FIFO is full.");

assert_no_underflow: assert property (@(posedge rd_clk) disable iff (!rd_rst_n)
        rd_en |-> !empty)
        else $error("Error: FIFO Underflow! Read attempted while FIFO is empty.");
endmodule
