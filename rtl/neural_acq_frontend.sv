module neural_acq_frontend #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4
) (
    input  logic                    sensor_clk, // NOTE: Connected to sys_clk in Top
    input  logic                    sensor_rst_n,
    
    input  logic [DATA_WIDTH-1:0]   adc_data_in,
    input  logic [CH_ID_WIDTH-1:0]  adc_channel_in,
    input  logic                    adc_valid_in,

    input logic                     ch_enable,

    output logic [DATA_WIDTH-1:0]   acq_data,
    output logic [CH_ID_WIDTH-1:0]  acq_channel,
    output logic                    acq_valid
);
    always_ff @(posedge sensor_clk or negedge sensor_rst_n) begin
        if (!sensor_rst_n) begin
            acq_data    <= '0;
            acq_channel <= '0;
            acq_valid   <= 1'b0;
        end else begin
            if (adc_valid_in && ch_enable) begin
                acq_data    <= adc_data_in;
                acq_channel <= adc_channel_in;
                acq_valid   <= 1'b1;
            end else begin
                acq_valid   <= 1'b0;
            end
        end
    end
assert_valid_propagation: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        adc_valid_in |=> acq_valid)
        else $error("Error: acq_valid not asserted after valid input.");
assert_data_integrity: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        adc_valid_in |=> (acq_data == $past(adc_data_in)))
        else $error("Error: Data mismatch (acq_data != past adc_data_in).");
assert_channel_integrity: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        adc_valid_in |=> (acq_channel == $past(adc_channel_in)))
        else $error("Error: Channel ID mismatch.");


endmodule
