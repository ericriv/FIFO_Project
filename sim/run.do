# ================================
# FIFO Simulation Run Script (run.do)
# Run from the sim/ directory
# ================================

# Clean and recreate work directory
vdel -all
vlib work

# Compile RTL, assertions, and testbench
vlog -sv ../rtl/fifo.sv
vlog -sv ../assertions/fifo_sva.sv
vlog -sv ../tb/fifo_tb.sv

# Run simulation (with limited optimization for waveform viewing)
vsim -voptargs=+acc work.fifo_tb 

# Record sim log
transcript file sim_output.log

# Plot waveform
add wave -r fifo_tb/*

# Run until completion
run -all

#quit -sim
