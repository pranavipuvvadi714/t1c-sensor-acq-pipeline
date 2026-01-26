module neural_aggregator #(
    parameter NUM_CHANNELS = 16,
    parameter DATA_WIDTH   = 16,
    parameter CH_ID_WIDTH  = 4
) (

    input  logic                     sensor_clk,
    input  logic                     sys_clk,
    input  logic                     rst_n,


    input  logic [NUM_CHANNELS-1:0]  channel_mask, 


    input  logic [DATA_WIDTH-1:0]    sensor_data_in [NUM_CHANNELS],
    input  logic                     sensor_valid_all, 


    output logic [DATA_WIDTH-1:0]    adc_data_out,
    output logic [CH_ID_WIDTH-1:0]    adc_channel_out,
    output logic                     adc_valid_out
);

    logic [DATA_WIDTH-1:0] shadow_regs [NUM_CHANNELS];

    always_ff @(posedge sensor_clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_CHANNELS; i++) shadow_regs[i] <= '0;
        end else if (sensor_valid_all) begin
            shadow_regs <= sensor_data_in; 
        end
    end

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
    assign start_sweep_pulse = sync_req_q2 && !sync_req_q3;

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
                if (channel_mask[rr_ptr] == 1'b1) begin
                    adc_data_out    <= shadow_regs[rr_ptr];
                    adc_channel_out <= rr_ptr;
                    adc_valid_out   <= 1'b1;
                end else begin
                    adc_valid_out   <= 1'b0; 
                end

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

assert_sweep_start: assert property (@(posedge sys_clk) disable iff (!rst_n)
        start_sweep_pulse && !is_sweeping |=> is_sweeping)
        else $error("Error: Sweep did not start after trigger pulse.");
endproperty

assert_mask_compliance: assert property (@(posedge sys_clk) disable iff (!rst_n)
        (is_sweeping && adc_valid_out) |-> channel_mask[adc_channel_out])
        else $error("Error: Valid asserted for a masked channel!");
endproperty

assert_rr_ptr_increment: assert property (@(posedge sys_clk) disable iff (!rst_n)
        (is_sweeping && rr_ptr < NUM_CHANNELS-1) |=> (rr_ptr == $past(rr_ptr) + 1'b1))
        else $error("Error: Internal rr_ptr did not increment sequentially.");
endproperty
endmodule
