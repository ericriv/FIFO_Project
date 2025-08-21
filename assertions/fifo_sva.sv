`define rd_ptr fifo_tb.my_fifo.rd_ptr
`define wr_ptr fifo_tb.my_fifo.wr_ptr
`define cnt fifo_tb.my_fifo.cnt

module fifo_sva #(
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

property check_reset;
	@(posedge clk) 
		(!rst_ |-> (`rd_ptr == 0 && `wr_ptr == 0 && cnt == 0 && empty && !full));
endproperty
check_resetP assert property (check_rest) else $display($stime,"\t\t FAIL::check_reset\n");
check_resetC cover property (check_rest) $display($stime,"\t\t PASS::check_reset\n");

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
check_fullP assert property (check_full) else $display($stime,"\t\t FAIL::check_full\n");
check_fullC cover property (check_full) $display($stime,"\t\t PASS::check_full\n");

property full_count;
	@(posedge clk) disable iff(!rst_)
		((full && wr_en && !rd_en) |-> ##1 $stable(`cnt));
endproperty
full_countP assert property (full_count) else $display($stime,"\t\t FAIL::full_count\n");
full_countC cover property (full_count) $display($stime,"\t\t PASS::full_count\n");

property full_wr_ptr;
	@(posedge clk) disable iff(!rst_)
		((full && wr_en && !rd_en) |-> ##1 $stable(`wr_ptr));
endproperty
full_wr_ptrP assert property (full_wr_ptr) else $display($stime,"\t\t FAIL::full_wr_ptr\n");
full_wr_ptrC cover property (full_wr_ptr) $display($stime,"\t\t PASS::full_wr_ptr\n");

property empty_count;
	@(posedge clk) disable iff(!rst_)
		((empty && rd_en && !wr_en) |-> ##1 $stable(`cnt));
endproperty
empty_countP assert property (empty_count) else $display($stime,"\t\t FAIL::empty_count\n");
empty_countC cover property (empty_count) $display($stime,"\t\t PASS::empty_count\n");

property empty_rd_ptr;
	@(posedge clk) disable iff(!rst_)
		((empty && rd_en && !wr_en) |-> ##1 $stable(`rd_ptr));
endproperty
empty_rd_ptrP assert property (empty_rd_ptr) else $display($stime,"\t\t FAIL::empty_rd_ptr\n");
empty_rd_ptrC cover property (empty_rd_ptr) $display($stime,"\t\t PASS::empty_rd_ptr\n");

property simul_count;
	@(posedge clk) disable iff(!rst_)
		((!empty && !full && rd_en && wr_en) |-> ##1 $stable(`cnt));
endproperty
simul_countP assert property (simul_count) else $display($stime,"\t\t FAIL::simul_count\n");
simul_countC cover property (simul_count) $display($stime,"\t\t PASS::simul_count\n");

property simul_count_empty;
	@(posedge clk) disable iff(!rst_)
		((empty && rd_en && wr_en) |-> ##1 (`cnt == $past(`cnt) + 1));
endproperty
simul_count_emptyP assert property (simul_count_empty) else $display($stime,"\t\t FAIL::simul_count_empty\n");
simul_count_emptyC cover property (simul_count_empty) $display($stime,"\t\t PASS::simul_count_empty\n");

property simul_count_full;
	@(posedge clk) disable iff(!rst_)
		((full && rd_en && wr_en) |-> ##1 (`cnt == $past(`cnt) - 1));
endproperty
simul_count_fullP assert property (simul_count_full) else $display($stime,"\t\t FAIL::simul_count_full\n");
simul_count_fullC cover property (simul_count_full) $display($stime,"\t\t PASS::simul_count_full\n");

endmodule