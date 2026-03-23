module fifo_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
) (
	input clock,
	input reset,
	input wr_en,
	input rd_en,
	input [DWIDTH-1:0] data_in,
	input f_full,
	input f_empty,
	input [DWIDTH-1:0] data_out
);

localparam MAX_COUNT = (1 << AWIDTH) - 1;

full_flag_at_max_count: assert property (@(posedge clock) disable iff (reset)
	f_full == (fifo.counter == MAX_COUNT));

empty_flag_at_zero_count: assert property (@(posedge clock) disable iff (reset)
	f_empty == (fifo.counter == 0));

no_write_when_full: assert property (@(posedge clock) disable iff (reset)
	f_full |-> !wr_en);

no_read_when_empty: assert property (@(posedge clock) disable iff (reset)
	f_empty |-> !rd_en);

counter_within_bounds: assert property (@(posedge clock) disable iff (reset)
	fifo.counter <= MAX_COUNT);

counter_increments_on_write_only: assert property (@(posedge clock) disable iff (reset)
	(wr_en && !f_full && !rd_en) |=> fifo.counter == $past(fifo.counter) + 1);

counter_decrements_on_read_only: assert property (@(posedge clock) disable iff (reset)
	(rd_en && !f_empty && !wr_en) |=> fifo.counter == $past(fifo.counter) - 1);

counter_stable_on_simultaneous_rw: assert property (@(posedge clock) disable iff (reset)
	(rd_en && wr_en && !f_empty && !f_full) |=> $stable(fifo.counter));

wr_ptr_resets_to_zero: assert property (@(posedge clock) reset |-> fifo.wr_ptr == 0);

rd_ptr_resets_to_zero: assert property (@(posedge clock) reset |-> fifo.rd_ptr == 0);

counter_resets_to_zero: assert property (@(posedge clock) reset |-> fifo.counter == 0);

wr_ptr_increments_on_write: assert property (@(posedge clock) disable iff (reset)
	(wr_en && !f_full) |=> fifo.wr_ptr == ($past(fifo.wr_ptr) + 1));

rd_ptr_increments_on_read: assert property (@(posedge clock) disable iff (reset)
	(rd_en && !f_empty) |=> fifo.rd_ptr == ($past(fifo.rd_ptr) + 1));

wr_ptr_stable_when_full: assert property (@(posedge clock) disable iff (reset)
	f_full |=> $stable(fifo.wr_ptr));

rd_ptr_stable_when_empty: assert property (@(posedge clock) disable iff (reset)
	f_empty |=> $stable(fifo.rd_ptr));

data_out_valid: assert property (@(posedge clock)
	data_out == fifo.mem[fifo.rd_ptr]);

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
