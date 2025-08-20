`define rd_ptr fifo_tb.my_fifo.rd_ptr
`define wrt_ptr fifo_tb.my_fifo.wrt_ptr
`define cnt fifo_tb.my_fifo.cnt

module fifo_property #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
	input  logic              			clk,
    input  logic              			rst_,
    input  logic               			wr_en,
    input  logic               			rd_en,
    input  logic	[DATA_WIDTH-1:0] 	din,
    input  logic	[DATA_WIDTH-1:0] 	dout,
    input  logic              			full,
    input  logic              			empty
);

property check_rest;
	@(posedge clk) 
		(!rst_ |-> (`rd_ptr == 0 && `wrt_ptr == 0 && cnt == 0 && empty && !full));
endproperty
check_restP assert property (check_rest) else $display($stime,"\t\t FAIL::check_rest\n");
check_restC cover property (check_rest) $display($stime,"\t\t PASS::check_rest\n");

property check_empty;
	@(posedge clk) disable iff(!rst_)
		(`cnt == 0 |-> empty);
endproperty
check_emptyP assert property (check_empty) else $display($stime,"\t\t FAIL::check_empty\n");
check_emptyC cover property (check_empty) $display($stime,"\t\t PASS::check_empty\n");


property check_full;
	@(posedge clk) disable iff(!rst_)
		(`cnt == DEPTH |-> full);
endproperty
check_fullP assert property (check_full) else $display($stime,"\t\t FAIL::check_full\n")
check_fullC cover property (check_full) $display($stime,"\t\t PASS::check_full\n")




endmodule