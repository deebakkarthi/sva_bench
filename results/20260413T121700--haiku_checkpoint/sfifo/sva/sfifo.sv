module sfifo_assert #(
	parameter DW = 8,
	parameter LGFLEN = 4
) (
	input wire i_clk, i_reset,
	input wire i_wr,
	input wire [DW-1:0] i_data,
	input wire o_full,
	input wire i_rd,
	input wire [DW-1:0] o_data,
	input wire o_empty,
	input wire o_err
);

full_empty_exclusive: assert property (@(posedge i_clk) disable iff (i_reset)
	~(o_full & o_empty));

full_condition: assert property (@(posedge i_clk)
	o_full |-> ((sfifo.wraddr[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0]) &
				(sfifo.wraddr[LGFLEN] != sfifo.rdaddr[LGFLEN])));

empty_condition: assert property (@(posedge i_clk)
	o_empty |-> (sfifo.rdaddr == sfifo.wraddr));

overflow_flag_set: assert property (@(posedge i_clk) disable iff (i_reset)
	(o_full & i_wr & ~i_rd) |-> ##1 o_err);

underflow_flag_set: assert property (@(posedge i_clk) disable iff (i_reset)
	(o_empty & i_rd) |-> ##1 o_err);

error_flag_accurate: assert property (@(posedge i_clk)
	o_err == (sfifo.r_ovfl | sfifo.r_unfl));

write_pointer_increments: assert property (@(posedge i_clk) disable iff (i_reset)
	(sfifo.w_wr) |-> (sfifo.wraddr == ($past(sfifo.wraddr) + 1)));

read_pointer_increments: assert property (@(posedge i_clk) disable iff (i_reset)
	(sfifo.w_rd) |-> (sfifo.rdaddr == ($past(sfifo.rdaddr) + 1)));

write_blocked_when_full: assert property (@(posedge i_clk) disable iff (i_reset)
	(o_full & ~i_rd & i_wr) |-> (sfifo.wraddr == $past(sfifo.wraddr)));

read_blocked_when_empty: assert property (@(posedge i_clk) disable iff (i_reset)
	(o_empty & i_rd) |-> (sfifo.rdaddr == $past(sfifo.rdaddr)));

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
