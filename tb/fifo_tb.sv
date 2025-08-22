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
		clk = 0;
		reset_fifo;
		repeat(2) @(posedge clk);
		
		//DT1: Fill -> Drain
		for(int i = 0; i < DEPTH; i++) begin 
			write_fifo(i);
		end
		@(posedge clk);
		for(int i = DEPTH-1; i >= 0; i--) begin
			read_fifo(val);
			$display("Read value: %0d",val);
		end
		
		//DT2: Write when full
		for(int i = 0; i <= DEPTH; i++) begin 
			write_fifo(i);
		end
		
		//DT3: Read when empty
		for(int i = DEPTH; i >= 0; i--) begin
			read_fifo(val);
			$display("Read value: %0d",val);
		end
		
		//DT4.1: Read and Write when empty
		read_write_fifo(val, val);
		
		//DT4.2: Read and Write when neither
		read_write_fifo(val, val);
		
		//DT4.3: Read and Write when full
		for(int i = 0; i < DEPTH; i++) begin 
			write_fifo(i);
		end
		read_write_fifo(val, val);
		
		repeat(2) @(posedge clk);
		$stop;
	end 
	
	always #5 clk = ~clk;
	
	
	//always @(posedge clk) $display($stime,,,"clk=%b, rst_=%b, wr_en=%b, rd_en=%b, din=%b, dout=%b, full=%b, empty=%b", 
	//clk, rst_, wr_en, rd_en, din, dout, full, empty);
	
	
	
	//=======================//
	//   Task Declarations   //
	//======================//
	
	task automatic reset_fifo;
		wr_en = 0;
		rd_en = 0;
		rst_ = 1;
		@(negedge clk) rst_ = 0;
		repeat(2) @(negedge clk);
		rst_ = 1;
	endtask
	
	task automatic write_fifo(input logic [DATA_WIDTH-1:0] val);
		@(negedge clk);
		wr_en = 1;
		rd_en = 0;
		din = val;
		@(negedge clk);
		wr_en = 0;
	endtask
	
	task automatic read_fifo(output logic [DATA_WIDTH-1:0] val);
		@(negedge clk);
		rd_en = 1;
		wr_en = 0;
		@(negedge clk)
		rd_en = 0;
		val = dout;
	endtask
	
	task automatic read_write_fifo(input logic [DATA_WIDTH-1:0] val_in,
								   output logic [DATA_WIDTH-1:0] val_out);
		@(negedge clk);
		rd_en = 1;
		wr_en = 1;
		din = val_in;
		@(negedge clk);
		rd_en = 0;
		wr_en = 0;
		val_out = dout;
	endtask

endmodule