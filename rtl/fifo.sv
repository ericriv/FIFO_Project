module fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input  logic              			clk,
    input  logic              			rst_,
    input  logic               			wr_en,
    input  logic               			rd_en,
    input  logic	[DATA_WIDTH-1:0] 	din,
    output logic	[DATA_WIDTH-1:0] 	dout,
    output logic              			full,
    output logic              			empty
);

	localparam ADDR_BITS = $clog2(DEPTH);

	logic	[DATA_WIDTH-1:0]	mem		[0:DEPTH-1];
	
	logic	[ADDR_BITS-1:0]		rd_ptr;
	logic	[ADDR_BITS-1:0]		wr_ptr;
	logic 	[ADDR_BITS:0]		cnt;

	always @(posedge clk or negedge rst_) begin
		if(!rst_) begin
			rd_ptr <= 0;
			wr_ptr <= 0;
			cnt <= 0;
			full <= 0;
			empty <= 1;
		end //if
		
		else begin
			case({wr_en,rd_en})
			
				2'b10: begin //write
					if(!full) begin
						mem[wr_ptr] <= din;
						wr_ptr <= (wr_ptr == DEPTH-1) ? 0 : wr_ptr + 1; //reset wr_ptr if at end of fifo
						full <= (cnt == DEPTH-1);
						cnt <= cnt + 1;
					end //if !full
				end //write
			
				2'b01: begin //read
					if(!empty) begin
						dout <= mem[rd_ptr];
						rd_ptr <= (rd_ptr == DEPTH-1) ? 0 : rd_ptr + 1; //reset rd_ptr if at end of fifo
						empty <= (cnt == 1);
						cnt <= cnt - 1;
					end //if !empty
				end //read
			
				2'b11: begin //read and write
					if(!full) begin //write
						mem[wr_ptr] <= din;
						wr_ptr <= (wr_ptr == DEPTH-1) ? 0 : wr_ptr + 1; //reset wr_ptr if at end of fifo
						if(empty) begin //read will not occur, need to increment cnt
							cnt <= cnt + 1;
							empty <= 0;
						end
					end
					
					if(!empty) begin //read
						dout <= mem[rd_ptr];
						rd_ptr <= (rd_ptr == DEPTH-1) ? 0 : rd_ptr + 1; //reset rd_ptr if at end of fifo
						if(full) begin //write will not occur, need to decrement cnt
							cnt <= cnt - 1;
							full <= 0;
						end
					end
				end //read and write
			
				default: ; 
			endcase
		end //else
	end //always
	
endmodule 