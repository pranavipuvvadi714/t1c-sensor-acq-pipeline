module neural_packet_framer #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4, 
    parameter PACKET_WIDTH= 64
) (
    input  logic                    sensor_clk, 
    input  logic                    sensor_rst_n,

    input  logic [DATA_WIDTH-1:0]   acq_data,
    input  logic [CH_ID_WIDTH-1:0]  acq_channel,
    input  logic                    acq_valid,

    output logic [PACKET_WIDTH-1:0] framed_packet,
    output logic                    framed_valid
);
    logic [31:0] timestamp_ctr;

    // Timestamp counts SYS_CLK cycles (higher resolution)
    always_ff @(posedge sensor_clk or negedge sensor_rst_n) begin
        if (!sensor_rst_n) begin
            timestamp_ctr <= '0;
        end 
        else begin
            timestamp_ctr <= timestamp_ctr + 1;
        end               
    end

    always_ff @(posedge sensor_clk or negedge sensor_rst_n) begin
        if (!sensor_rst_n) begin
            framed_packet <= '0;
            framed_valid  <= 1'b0;
        end else begin
            framed_valid <= acq_valid;
            if (acq_valid) begin
                // [63:32] TS, [31:28] CH, [27:12] Data, [11:0] Zero
                framed_packet <= {timestamp_ctr, acq_channel, acq_data, 12'h000};
            end else begin
                framed_packet <='0;
            end
        end
    end
assert_timer_increment: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        timestamp_ctr == $past(timestamp_ctr) + 1)
        else $error("Error: Timestamp counter did not increment correctly.");

assert_frame_valid_prop: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        acq_valid |=> framed_valid)
        else $error("Error: framed_valid did not assert after acq_valid.");


endmodule
