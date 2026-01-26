/*module neural_acq_frontend #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4
) (
    input  logic                   sensor_clk,
    input  logic                   sensor_rst_n,
    
    // Physical Sensor Interface
    input  logic [DATA_WIDTH-1:0]  adc_data_in,
    input  logic [CH_ID_WIDTH-1:0] adc_channel_in, // Assuming Muxed input
    input  logic                   adc_valid_in,

    // Control
    input  logic                   ch_enable,      // CSR control

    // Output to Framer
    output logic [DATA_WIDTH-1:0]  acq_data,
    output logic [CH_ID_WIDTH-1:0] acq_channel,
    output logic                   acq_valid
);

    always_ff @(posedge sensor_clk or negedge sensor_rst_n) begin
        if (!sensor_rst_n) begin
            acq_data    <= '0;
            acq_channel <= '0;
            acq_valid   <= 1'b0;
        end else begin
            // Clock Gating Logic: Only toggle internal pipeline if enabled
            // This saves power in implantable contexts.
            if (ch_enable && adc_valid_in) begin
                acq_data    <= adc_data_in;
                acq_channel <= adc_channel_in;
                acq_valid   <= 1'b1;
            end else begin
                acq_valid   <= 1'b0;
            end
        end
    end

// --- Formal Verification / Assertions ---
    // Capture: Valid signal should only be high if enabled and ADC was valid
    assert_capture: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        (adc_valid_in && ch_enable) |=> acq_valid)
        else $error("Capture logic failed: acq_valid did not follow enable/adc_valid");

    // Integrity: acq_data must match the previous cycle's adc_data_in
    assert_data_match: assert property (@(posedge sensor_clk) disable iff (!sensor_rst_n)
        (adc_valid_in && ch_enable) |=> (acq_data == $past(adc_data_in)))
        else $error("Data Mismatch: acq_data != $past(adc_data_in)");

endmodule*/

module neural_acq_frontend #(
    parameter DATA_WIDTH = 16,
    parameter CH_ID_WIDTH = 4
) (
    input  logic                    sensor_clk, // NOTE: Connected to sys_clk in Top
    input  logic                    sensor_rst_n,
    
    input  logic [DATA_WIDTH-1:0]   adc_data_in,
    input  logic [CH_ID_WIDTH-1:0]  adc_channel_in,
    input  logic                    adc_valid_in,
    input  logic                    ch_enable,

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
            if (ch_enable && adc_valid_in) begin
                acq_data    <= adc_data_in;
                acq_channel <= adc_channel_in;
                acq_valid   <= 1'b1;
            end else begin
                acq_valid   <= 1'b0;
            end
        end
    end
endmodule