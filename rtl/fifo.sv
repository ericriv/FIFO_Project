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
	
	logic	[ADDR_BITS:0]		rd_ptr;
	logic	[ADDR_BITS:0]		wrt_ptr;
	logic 	[ADDR_BITS:0]		cnt;

	always @(posedge clk or negedge rst_) begin
		if(!rst_) begin
			rd_ptr <= 0;
			wrt_ptr <= 0;
			cnt <= 0;
			full <= 0;
			empty <= 1;
		end //if
		
		else begin
			case({wr_en,rd_en})
			
				2'b10: begin //write
					if(!full) begin
						mem[wrt_ptr] <= din;
						cnt <= cnt + 1;
						wrt_ptr <= (wrt_ptr == DEPTH) ? 0 : wrt_prt + 1; //reset wrt_prt if at end of fifo
						if(cnt == DEPTH-1) begin
							full <= 1;
						end 
					end //if !full
				end //write
			
				2'b01: begin //read
					if(!empty) begin
						rd_ptr <= (rd_ptr == DEPTH) ? 0 : rd_ptr + 1; //reset rd_ptr if at end of fifo
						cnt <= cnt - 1;
						if(cnt == 1) begin
							empty <= 1;
						end
					end //if !empty
				end //read
			
				2'b11 begin //read and write
					mem[wrt_ptr] <= din;
					wrt_ptr <= (wrt_ptr == DEPTH) ? 0 : wrt_prt + 1; //reset wrt_prt if at end of fifo
					rd_ptr <= (rd_ptr == DEPTH) ? 0 : rd_ptr + 1; //reset rd_ptr if at end of fifo
				end
			
				default: ; 
			endcase
		end //else
	end //always
	
	assign dout = mem[rd_ptr];

endmodule 