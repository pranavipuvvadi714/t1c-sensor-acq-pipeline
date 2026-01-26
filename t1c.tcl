clear -all

# ------------------------------------------------------------------------------
# 1. Analyze RTL Files
#    (Loading all dependencies using SystemVerilog 2009 standard)
# ------------------------------------------------------------------------------
analyze -sv09 rtl/asyncfifo.sv
analyze -sv09 rtl/neural_aggregator.sv
analyze -sv09 rtl/neural_acq_frontend.sv
analyze -sv09 rtl/neural_packet_framer.sv
analyze -sv09 rtl/top_module.sv

# ------------------------------------------------------------------------------
# 2. Elaborate Top Module
# ------------------------------------------------------------------------------
elaborate -top neural_acq_top

# ------------------------------------------------------------------------------
# 3. Clock Definitions
#    (Top module has 3 distinct clock domains)
# ------------------------------------------------------------------------------
clock sys_clk
clock sensor_clk
clock out_clk

# ------------------------------------------------------------------------------
# 4. Reset Definitions
#    (Resets are Active Low, so we use an expression to invert them for the tool)
#    The tool asserts these expressions to put the DUT in reset.
# ------------------------------------------------------------------------------
reset -expression { !sys_rst_n }
reset -expression { !sensor_rst_n }
reset -expression { !out_rst_n }

# Optional: Set up proof engine defaults
# prove -all
