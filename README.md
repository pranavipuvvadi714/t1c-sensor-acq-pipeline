# t1c-sensor-acq-pipeline

Hardware-based acquisition and buffering pipeline for digitized neural samples.

## Quick Start

### Running Simulations with VSIM

To run simulations using vsim:

1) Open ModelSim by typing vsim in your terminal.

2) Add Files: Project > Add to Project > Existing File...

3) Select all files from the rtl/ folder.

4) Select the testbench from the tb/ folder (e.g., tb/tb_simple_neural.sv).

5) Compile: Compile > Compile All. Ensure there are no errors.

6) Start Simulation: Simulate > Start Simulation...

7) Expand the work library and select the top-level testbench (tb_simple_neural).

8) Click OK.

9) Add Waves: Right-click the instance in the "Sim" tab -> Add to > Wave > All items in region.

10) Run: Type run -all in the transcript window or click the "Run -All" icon.

The simulation log in the transcript window will display the test progress, CSR operations, data input/output, and final status.

###Running Formal verification with Jaspergold
To run formal verification assertions:

1) Launch JasperGold:
```bash
jaspergold
```
2) Source the Script: In the JasperGold console, source the provided TCL script:
```bash
source t1c.tcl
```

3)Run Proofs: Once the design is analyzed and elaborated, run all assertions:
```bash
prove -all
```

## Overview

This project implements a multi-clock domain neural signal acquisition pipeline that captures parallel ADC data from 16 channels, processes it through a round-robin aggregator, frames it into packets with timestamps, and buffers it in an asynchronous FIFO for output. The design supports configurable channel masking and includes a Control Status Register (CSR) interface for system control and monitoring.

## Architecture

The pipeline consists of four main stages operating across three clock domains:

```
Sensor Domain (sensor_clk) → System Domain (sys_clk) → Output Domain (out_clk)
     ↓                              ↓                        ↓
[16 ADCs] → [Aggregator] → [Frontend] → [Framer] → [Async FIFO] → [Output]
```

![Data Path Architecture](<docs/images/Flowchart - Page 1 datapath.png>)

### Clock Domains

1. **Sensor Clock Domain** (`sensor_clk`): Slow clock domain (e.g., 32 kHz) where parallel ADC data is captured
2. **System Clock Domain** (`sys_clk`): Fast clock domain (e.g., 1 MHz) where processing occurs
3. **Output Clock Domain** (`out_clk`): Variable clock domain (e.g., SPI rate) for output interface

## Module Descriptions

### 1. `neural_acq_top` (Top Module)

**Location**: `rtl/top_module.sv`

The top-level module that integrates all pipeline components.

**Key Features**:
- Three independent clock domains with proper reset handling
- Parallel input interface for 16 ADC channels (16-bit data each)
- CSR interface for configuration and status monitoring
- Handshake-based output interface (64-bit data with valid/ready signals)

**Parameters**:
- `DATA_WIDTH = 16`: Width of ADC data samples
- `CH_ID_WIDTH = 4`: Width of channel identifier (supports up to 16 channels)
- `NUM_CHANNELS = 16`: Number of parallel ADC channels

**CSR Register Map**:
- **Address 0x0**: Global Enable Register
  - Bit [0]: Master enable for the acquisition pipeline
- **Address 0x1**: Status Register (Read-only)
  - Bit [0]: FIFO Empty flag (synchronized)
  - Bit [1]: FIFO Full flag
  - Bit [2]: Sticky Overflow flag (set when FIFO overflows)
- **Address 0x2**: Channel Mask Register
  - Bits [15:0]: Individual channel enable mask (1 = enabled, 0 = masked)

### Control Status Register (CSR) Interface

The CSR interface provides control and status monitoring for the acquisition pipeline. All CSR operations operate on the system clock domain (`sys_clk`).

**CSR Write Interface** (`csr_wdata`):
![CSR Write Data Flow](<docs/images/Flowchart - Page 1 csr_wdata.png>)

**CSR Read Interface** (`csr_rdata`):
![CSR Read Data Flow](<docs/images/Flowchart - Page 1 csr_rdata.png>)

**Register Details**:

1. **Address 0x0 - Global Enable Register** (Read/Write)
   - **Bit [0]**: `reg_global_enable` - Master enable bit for the acquisition pipeline
   - **Bits [31:1]**: Reserved (read as 0)
   - **Default**: 0x0 (disabled)
   - **Usage**: Set bit 0 to enable data acquisition and processing

2. **Address 0x1 - Status Register** (Read-only)
   - **Bit [0]**: `fifo_empty_sync2` - FIFO empty flag (synchronized from output clock domain)
   - **Bit [1]**: `fifo_full` - FIFO full flag (indicates buffer is full)
   - **Bit [2]**: `reg_overflow_sticky` - Sticky overflow flag (set when FIFO overflows, remains set until cleared)
   - **Bits [31:3]**: Reserved (read as 0)
   - **Usage**: Monitor pipeline status and detect overflow conditions

3. **Address 0x2 - Channel Mask Register** (Read/Write)
   - **Bits [15:0]**: `reg_channel_mask` - Per-channel enable mask
     - Bit [N] = 1: Channel N is enabled (data will be processed)
     - Bit [N] = 0: Channel N is masked (data will be filtered out)
   - **Bits [31:16]**: Reserved (read as 0)
   - **Default**: 0xFFFF (all channels enabled)
   - **Usage**: Selectively enable/disable individual ADC channels for power savings or debugging

**CSR Interface Signals**:
- `csr_addr[2:0]`: 3-bit address (supports 8 registers)
- `csr_write`: Write enable signal (active high)
- `csr_wdata[31:0]`: 32-bit write data
- `csr_rdata[31:0]`: 32-bit read data

**Notes**:
- All CSR operations are synchronous to `sys_clk`
- The overflow flag is sticky and must be cleared by reset
- Channel mask defaults to all channels enabled (0xFFFF) on reset
- FIFO empty flag is synchronized from the output clock domain to prevent metastability

### 2. `neural_aggregator`

**Location**: `rtl/neural_aggregator.sv`

![Neural Aggregator Flowchart](<docs/images/Flowchart - Page 1 neural_aggregator.png>)

Bridges the sensor clock domain to the system clock domain by implementing a round-robin sweep mechanism.

**Functionality**:
- Captures parallel ADC data into shadow registers on `sensor_valid_all` assertion
- Synchronizes capture trigger from `sensor_clk` to `sys_clk` using a 3-stage synchronizer
- Performs round-robin sweep through enabled channels (based on `channel_mask`)
- Outputs serialized data with channel ID and valid signal on `sys_clk`

**Key Signals**:
- `sensor_data_in[NUM_CHANNELS]`: Parallel input array from ADCs
- `sensor_valid_all`: Strobe signal indicating all channels have valid data
- `channel_mask`: Per-channel enable mask (from CSR)
- `adc_data_out`, `adc_channel_out`, `adc_valid_out`: Serialized output stream

### 3. `neural_acq_frontend`

**Location**: `rtl/neural_acq_frontend.sv`

![Neural Acquisition Frontend Flowchart](<docs/images/Flowchart - Page 1 neural_acq_frontend.png>)

Processing stage that operates on the system clock domain.

**Functionality**:
- Simple pipeline register that forwards data from aggregator to framer
- Validates and propagates valid signals
- Operates as a pass-through stage in the current implementation

**Interface**:
- Input: `adc_data_in`, `adc_channel_in`, `adc_valid_in`
- Output: `acq_data`, `acq_channel`, `acq_valid`

### 4. `neural_packet_framer`

**Location**: `rtl/neural_packet_framer.sv`

![Neural Packet Framer Flowchart](<docs/images/Flowchart - Page 1 neural_packet_framer.png>)

Packetizes acquisition data into 64-bit frames with timestamps.

**Packet Format**:
```
[63:32]  Timestamp (32-bit system clock counter)
[31:28]  Channel ID (4-bit)
[27:12]  ADC Data (16-bit)
[11:0]   Reserved (zero-padded)
```

**Functionality**:
- Maintains a 32-bit timestamp counter that increments on every `sys_clk` cycle
- Formats incoming data into 64-bit packets
- Outputs framed packets with valid signal

**Parameters**:
- `PACKET_WIDTH = 64`: Width of output packet

### 5. `async_fifo`

**Location**: `rtl/asyncfifo.sv`

![Asynchronous FIFO Flowchart](<docs/images/Flowchart - Page 1 async_fifo.png>)

Asynchronous FIFO that bridges the system clock domain to the output clock domain.

**Functionality**:
- Implements a dual-clock FIFO using Gray code pointers for safe clock domain crossing
- Provides full/empty flags for flow control
- Configurable depth (default: 32 entries, `DEPTH_LOG2 = 5`)

**Features**:
- Write side operates on `wr_clk` (system clock)
- Read side operates on `rd_clk` (output clock)
- Gray code encoding prevents metastability issues during pointer synchronization
- Separate reset signals for each clock domain

**Parameters**:
- `DATA_WIDTH = 64`: Width of data words
- `DEPTH_LOG2 = 5`: Log2 of FIFO depth (depth = 2^DEPTH_LOG2)

## Testbenches

### 1. `tb_simple_neural` (Top-Level Testbench)

**Location**: `tb/tb_top.sv`

Comprehensive testbench for the complete pipeline.

**Test Features**:
- Multi-clock domain simulation (sensor_clk: 1 MHz, sys_clk: 50 MHz, out_clk: 25 MHz)
- CSR read/write verification
- Channel mask configuration and testing
- Input/output data monitoring
- Status register verification

**Test Sequence**:
1. System reset and initialization
2. CSR write to enable the system (Address 0x0)
3. CSR write to configure channel mask (Address 0x2)
4. CSR readback verification
5. Multiple data burst captures with different patterns
6. Final status check via CSR

### 2. `neural_aggregator_tb` (Unit Testbench)

**Location**: `tb/neural_aggregator_tb.sv`

Unit testbench for the aggregator module in isolation.

**Test Features**:
- Isolated testing of clock domain crossing
- Channel mask functionality verification
- Scoreboard-based data verification
- Random data and mask generation
- Simulation logging to file

**Verification**:
- Compares output data against shadow truth registers
- Tracks match/error counts
- Generates detailed simulation logs

## Design Considerations

### Clock Domain Crossing (CDC)

The design implements multiple CDC boundaries:
1. **Sensor → System**: Handled by `neural_aggregator` using shadow registers and synchronizers
2. **System → Output**: Handled by `async_fifo` using Gray code pointers

### Channel Masking

The channel mask register allows selective processing of ADC channels, enabling:
- Power savings by disabling unused channels
- Flexible channel configuration
- Debug and diagnostic capabilities

### Flow Control

- **Input**: `sensor_valid_all` strobe indicates when all channels have valid data
- **Output**: Handshake protocol using `dout_valid` and `dout_ready`
- **FIFO**: Full/empty flags prevent data loss and indicate buffer status

### Error Handling

- **Sticky Overflow Flag**: Set when FIFO becomes full while new data arrives
- **Status Monitoring**: CSR provides real-time FIFO status
- **Synchronized Flags**: Status flags are properly synchronized to prevent metastability

## Simulation

The testbenches use SystemVerilog code with:
- `timescale 1ns/1ps`
- Clock generation using `forever` loops
- Scoreboard-based verification
- Comprehensive logging

## File Structure

```
t1c-sensor-acq-pipeline/
├── rtl/
│   ├── top_module.sv              # Top-level integration module
│   ├── neural_aggregator.sv        # Clock domain crossing aggregator
│   ├── neural_acq_frontend.sv     # Processing frontend
│   ├── neural_packet_framer.sv    # Packet formatter
│   └── asyncfifo.sv               # Asynchronous FIFO
├── tb/
│   ├── tb_top.sv                  # Top-level testbench
│   └── neural_aggregator_tb.sv    # Aggregator unit testbench
├── docs/
│   └── images/                    # Architecture and module flowcharts
├── Makefile                       # Simulation build system
└── README.md                      # This file
```

## Parameters Summary

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 16 | Width of ADC data samples |
| `CH_ID_WIDTH` | 4 | Width of channel identifier |
| `NUM_CHANNELS` | 16 | Number of parallel ADC channels |
| `PACKET_WIDTH` | 64 | Width of output packets |
| `DEPTH_LOG2` | 5 | Log2 of FIFO depth (32 entries) |

## Applications

This pipeline is designed for:
- Neural signal acquisition systems
- Multi-channel data acquisition
- Implantable medical devices
- Low-power sensor interfaces
- Real-time data streaming applications

