# ================================
# FIFO Simulation Run Script (run.do)
# Run from the sim/ directory
# ================================

# Create/clean work library
vdel -all
vlib work

# Compile RTL, assertions, and testbench
vlog -sv ../rtl/fifo.sv
vlog -sv ../assertions/fifo_sva.sv
vlog -sv ../tb/fifo_tb.sv

# Run simulation, log output to file
vsim work.fifo_tb -l sim_output.log

# Record all signals to wave
log -r /*
add wave -r /*

# Run until completion
run -all
