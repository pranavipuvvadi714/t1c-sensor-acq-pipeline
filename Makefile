# Makefile for t1c-sensor-acq-pipeline
# Supports both VCS (Synopsys) and ModelSim/QuestaSim (vsim) simulators

# ============================================================================
# Configuration
# ============================================================================

# Directories
RTL_DIR := rtl
TB_DIR  := tb
WORK_DIR := work
VCS_DIR  := vcs_work
VSIM_DIR := vsim_work

# Source files - automatically use all .sv files in rtl (excluding .bak files)
RTL_FILES := $(filter-out %.bak,$(wildcard $(RTL_DIR)/*.sv))

TB_TOP := $(TB_DIR)/tb_top.sv
TB_UNIT := $(TB_DIR)/neural_aggregator_tb.sv

# Paths relative to VCS_DIR (for when we cd into vcs_work)
RTL_FILES_VCS := $(addprefix ../,$(RTL_FILES))
TB_TOP_VCS := ../$(TB_TOP)
TB_UNIT_VCS := ../$(TB_UNIT)

# Testbench top modules
TB_TOP_MODULE := tb_simple_neural
TB_UNIT_MODULE := neural_aggregator_tb

# Simulator executables (adjust paths as needed)
VCS := vcs
VSIM := vsim
VLIB := vlib
VMAP := vmap

# VCS options
VCS_OPTS := -full64 \
            -sverilog \
            -timescale=1ns/1ps \
            -debug_access+all \
            -lca \
            -kdb

# vsim options
VSIM_OPTS := -voptargs=+acc \
             -t 1ps \
             -do "run -all; quit -f"

# ============================================================================
# VCS Targets
# ============================================================================

.PHONY: sim-vcs-top sim-vcs-unit clean-vcs help-vcs

# VCS: Compile and simulate top-level testbench
sim-vcs-top: $(VCS_DIR)/$(TB_TOP_MODULE)
	@echo "=========================================="
	@echo "Running VCS simulation: Top-level testbench"
	@echo "=========================================="
	cd $(VCS_DIR) && ./$(TB_TOP_MODULE) -l sim_top.log 2>&1 | tee sim_top_console.log

# VCS: Compile and simulate unit testbench
sim-vcs-unit: $(VCS_DIR)/$(TB_UNIT_MODULE)
	@echo "=========================================="
	@echo "Running VCS simulation: Unit testbench"
	@echo "=========================================="
	cd $(VCS_DIR) && ./$(TB_UNIT_MODULE) -l sim_unit.log 2>&1 | tee sim_unit_console.log

# VCS: Compile top-level testbench
$(VCS_DIR)/$(TB_TOP_MODULE): $(RTL_FILES) $(TB_TOP)
	@echo "=========================================="
	@echo "VCS: Compiling top-level testbench"
	@echo "=========================================="
	@echo "RTL Files: $(RTL_FILES_VCS)"
	@mkdir -p $(VCS_DIR)
	cd $(VCS_DIR) && $(VCS) $(VCS_OPTS) \
		-top $(TB_TOP_MODULE) \
		-o $(TB_TOP_MODULE) \
		$(RTL_FILES_VCS) $(TB_TOP_VCS) \
		-l compile_top.log

# VCS: Compile unit testbench
$(VCS_DIR)/$(TB_UNIT_MODULE): $(RTL_FILES) $(TB_UNIT)
	@echo "=========================================="
	@echo "VCS: Compiling unit testbench"
	@echo "=========================================="
	@echo "RTL Files: $(RTL_FILES_VCS)"
	@mkdir -p $(VCS_DIR)
	cd $(VCS_DIR) && $(VCS) $(VCS_OPTS) \
		-top $(TB_UNIT_MODULE) \
		-o $(TB_UNIT_MODULE) \
		../$(RTL_DIR)/neural_aggregator.sv $(TB_UNIT_VCS) \
		-l compile_unit.log

# VCS: Clean generated files
clean-vcs:
	@echo "Cleaning VCS generated files..."
	rm -rf $(VCS_DIR)
	rm -rf csrc
	rm -rf ucli.key
	rm -rf vc_hdrs.h
	rm -rf DVEfiles
	rm -rf inter.vpd
	rm -rf vpdplus.vpd
	rm -rf *.vpd
	rm -rf *.log
	@echo "VCS cleanup complete."

# ============================================================================
# ModelSim/QuestaSim Targets
# ============================================================================

.PHONY: sim-vsim-top sim-vsim-unit compile-vsim-top compile-vsim-unit clean-vsim help-vsim

# vsim: Compile and simulate top-level testbench
sim-vsim-top: compile-vsim-top
	@echo "=========================================="
	@echo "Running vsim simulation: Top-level testbench"
	@echo "=========================================="
	cd $(VSIM_DIR) && $(VSIM) $(VSIM_OPTS) \
		$(TB_TOP_MODULE) \
		-l sim_top.log

# vsim: Compile and simulate unit testbench
sim-vsim-unit: compile-vsim-unit
	@echo "=========================================="
	@echo "Running vsim simulation: Unit testbench"
	@echo "=========================================="
	cd $(VSIM_DIR) && $(VSIM) $(VSIM_OPTS) \
		$(TB_UNIT_MODULE) \
		-l sim_unit.log

# vsim: Compile top-level testbench  
compile-vsim-top: $(VSIM_DIR)/work
	@echo "=========================================="
	@echo "vsim: Compiling top-level testbench"
	@echo "=========================================="
	@echo "RTL Files: $(RTL_FILES)"
	@rm -f $(VSIM_DIR)/compile_top.do
	@echo "# Auto-generated compile script" > $(VSIM_DIR)/compile_top.do
	@$(foreach file,$(RTL_FILES),echo "vlog -sv ../$(file);" >> $(VSIM_DIR)/compile_top.do;)
	@echo "vlog -sv ../$(TB_TOP);" >> $(VSIM_DIR)/compile_top.do
	@echo "quit -f" >> $(VSIM_DIR)/compile_top.do
	cd $(VSIM_DIR) && $(VSIM) -c -do compile_top.do -l compile_top.log

# vsim: Compile unit testbench
compile-vsim-unit: $(VSIM_DIR)/work
	@echo "=========================================="
	@echo "vsim: Compiling unit testbench"
	@echo "=========================================="
	@rm -f $(VSIM_DIR)/compile_unit.do
	@echo "# Auto-generated compile script" > $(VSIM_DIR)/compile_unit.do
	@echo "vlog -sv ../$(RTL_DIR)/neural_aggregator.sv;" >> $(VSIM_DIR)/compile_unit.do
	@echo "vlog -sv ../$(TB_UNIT);" >> $(VSIM_DIR)/compile_unit.do
	@echo "quit -f" >> $(VSIM_DIR)/compile_unit.do
	cd $(VSIM_DIR) && $(VSIM) -c -do compile_unit.do -l compile_unit.log

# vsim: Create work library
$(VSIM_DIR)/work:
	@echo "Creating vsim work library..."
	@mkdir -p $(VSIM_DIR)
	cd $(VSIM_DIR) && $(VLIB) work
	cd $(VSIM_DIR) && $(VMAP) work work

# vsim: Clean generated files
clean-vsim:
	@echo "Cleaning vsim generated files..."
	rm -rf $(VSIM_DIR)
	rm -rf $(WORK_DIR)
	rm -rf transcript
	rm -rf vsim.wlf
	rm -rf *.wlf
	rm -rf *.log
	rm -rf etch*
	rm -rf *.mti
	rm -rf *.mpf
	rm -rf wlft*
	@echo "vsim cleanup complete."

# ============================================================================
# General Targets
# ============================================================================

.PHONY: clean help all

# Clean all generated files
clean: clean-vcs clean-vsim
	@echo "Cleaning additional generated files..."
	rm -rf $(WORK_DIR)
	rm -rf etch*
	rm -rf *.mti
	rm -rf *.mpf
	rm -rf wlft*
	@echo "All cleanup complete."

# Help message
help:
	@echo "=========================================="
	@echo "t1c-sensor-acq-pipeline Makefile"
	@echo "=========================================="
	@echo ""
	@echo "VCS (Synopsys) Targets:"
	@echo "  make sim-vcs-top      - Compile and run top-level testbench"
	@echo "  make sim-vcs-unit     - Compile and run unit testbench"
	@echo "  make clean-vcs        - Clean VCS generated files"
	@echo ""
	@echo "ModelSim/QuestaSim (vsim) Targets:"
	@echo "  make sim-vsim-top    - Compile and run top-level testbench"
	@echo "  make sim-vsim-unit   - Compile and run unit testbench"
	@echo "  make compile-vsim-top - Compile top-level testbench only"
	@echo "  make compile-vsim-unit - Compile unit testbench only"
	@echo "  make clean-vsim      - Clean vsim generated files"
	@echo ""
	@echo "General Targets:"
	@echo "  make clean           - Clean all generated files"
	@echo "  make help            - Show this help message"
	@echo ""

# Default target
all: help

