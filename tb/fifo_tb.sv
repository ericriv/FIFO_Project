module fifo_tb;

	parameter DATA_WIDTH = 8;
	parameter DEPTH = 16;

	logic              			clk;
	logic              			rst_;
	logic               		wr_en;
	logic               		rd_en;
	logic	[DATA_WIDTH-1:0] 	din;
	wire	[DATA_WIDTH-1:0] 	dout;
	wire             			full;
	wire              			empty;
	
	fifo #(DATA_WIDTH, DEPTH) my_fifo(.clk, .rst_, .wr_en, .rd_en, .din, .dout, .full, .empty);
	
	bind fifo fifo_sva #(DATA_WIDTH, DEPTH) my_fifo_bind
	(.clk, .rst_, .wr_en, .rd_en, .din, .dout, .full, .empty);
	
	
	initial begin
		logic [DATA_WIDTH-1:0] val;
		
		rst_ = 0;
		clk = 0;
		repeat(2) @(posedge clk);
		rst_ = 1;
		for(int i = 0; i < DEPTH; i++) begin
			write_fifo(i);
		end
		@(posedge clk);
		for(int i = 0; i < DEPTH; i++) begin
			read_fifo(val);
			$display("Read value: %0d",val);
		end
		$stop;
	end 
	
	always begin
		#5 clk = ~clk;
	end	
	
	task automatic write_fifo(input logic [DATA_WIDTH-1:0] val);
		@(posedge clk);
		wr_en = 1;
		rd_en = 1;
		din = val;
		@(posedge clk);
		wr_en = 0;
	endtask
	
	task automatic read_fifo(output logic [DATA_WIDTH-1:0] val);
		@(posedge clk);
		rd_en = 1;
		wr_en = 0;
		@(posedge clk)
		rd_en = 0;
		val = dout;
	endtask
	

endmodule