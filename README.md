# FIFO_Project
Implementation of classic RTL module with the addition of SystemVerilog Assertions (SVA). 

## Block Diagram
![Block Diagram](docs/FIFO_BD.svg)

## DUT
- FIFO with parameterizable depth/width
- asynchronous reset
- 
- Ports: clk, rst, wr_en, rd_en, din, dout, full, empty

## Verification Objectives
- Verify correct reset behavior
- Verify functional correctness under push, pop, and simultaneous operations
- Verify corner cases (underflow, overflow, wrap-around)

## SVA
- Ensure proper reset functionality
- Ensure empty signal is asserted at the same clock fifo empties 
- Ensure full signal is asserted on same clock that fifo fills
- Ensure that count is not incremented on write (and not read) when full
- Ensure that wr_ptr is not incremented on write (and not read) when full
- Ensure that count is not decremented on read (and not write) when empty
- Ensure that rd_ptr is not incremented on read (and not write) when empty
- Ensure that count is not changed on simultaneous read and write (when not full or empty)
- Ensure count is incremented on simultaneous read and write when empty (read will not occur)
- Ensure count is decremented on simultaneous read and write when full (write will not occur)

## Testbench Strategy
- Directed Tests
  - Fill -> Drain
  - Write when full
  - Read when empty
  - Simultaneous read and write when:
    - empty
	- neither
	- full
  
- Randomized Tests
  - Random push/pop sequences
  - Stress test with long random streams