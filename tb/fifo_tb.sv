module fifo_tb;

	parameter DATA_WIDTH = 8,
	parameter DEPTH = 16

	logic              			clk;
	logic              			rst_;
	logic               		wr_en;
	logic               		rd_en;
	logic	[DATA_WIDTH-1:0] 	din;
	wire	[DATA_WIDTH-1:0] 	dout;
	wire             			full;
	wire              			empty;
	
	fifo #(.DATA_WIDTH, .DEPTH) my_fifo(.clk, .rst_, .wr_en, .rd_en, .din, .dout, .full, .empty);
	
	bind fifo fifo_sva #(.DATA_WIDTH, .DEPTH) my_fifo_bind
	(.clk, .rst_, .wr_en, .rd_en, .din, .dout, .full, .empty);
	
	


endmodule