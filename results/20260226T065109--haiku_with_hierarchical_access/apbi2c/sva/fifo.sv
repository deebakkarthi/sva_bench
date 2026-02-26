module fifo_assert
#(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock, reset, wr_en, rd_en,
	input [DWIDTH-1:0] data_in,
	output f_full, f_empty,
	output [DWIDTH-1:0] data_out
);

a_reset_clears_wr_ptr: assert property (@(posedge clock) reset |=> fifo.wr_ptr == 0);
a_reset_clears_rd_ptr: assert property (@(posedge clock) reset |=> fifo.rd_ptr == 0);
a_reset_clears_counter: assert property (@(posedge clock) reset |=> fifo.counter == 0);
a_reset_asserts_empty: assert property (@(posedge clock) reset |=> f_empty == 1'b1);
a_reset_deasserts_full: assert property (@(posedge clock) reset |=> f_full == 1'b0);

a_wr_ptr_increments_on_write: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full) |=> fifo.wr_ptr == ($past(fifo.wr_ptr) + 1));
a_wr_ptr_holds_when_disabled: assert property (@(posedge clock) disable iff (reset) (!wr_en) |=> fifo.wr_ptr == $past(fifo.wr_ptr));
a_wr_ptr_holds_when_full: assert property (@(posedge clock) disable iff (reset) (f_full) |=> fifo.wr_ptr == $past(fifo.wr_ptr));
a_wr_ptr_wraps_around: assert property (@(posedge clock) disable iff (reset) ((fifo.wr_ptr == {AWIDTH{1'b1}}) && wr_en && !f_full) |=> fifo.wr_ptr == 0);

a_rd_ptr_increments_on_read: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty) |=> fifo.rd_ptr == ($past(fifo.rd_ptr) + 1));
a_rd_ptr_holds_when_disabled: assert property (@(posedge clock) disable iff (reset) (!rd_en) |=> fifo.rd_ptr == $past(fifo.rd_ptr));
a_rd_ptr_holds_when_empty: assert property (@(posedge clock) disable iff (reset) (f_empty) |=> fifo.rd_ptr == $past(fifo.rd_ptr));
a_rd_ptr_wraps_around: assert property (@(posedge clock) disable iff (reset) ((fifo.rd_ptr == {AWIDTH{1'b1}}) && rd_en && !f_empty) |=> fifo.rd_ptr == 0);

a_counter_increments_on_write_only: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full && !rd_en) |=> fifo.counter == ($past(fifo.counter) + 1));
a_counter_decrements_on_read_only: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty && !wr_en) |=> fifo.counter == ($past(fifo.counter) - 1));
a_counter_holds_on_no_operation: assert property (@(posedge clock) disable iff (reset) ((!wr_en && !rd_en) || (wr_en && f_full) || (rd_en && f_empty)) |=> fifo.counter == $past(fifo.counter));
a_counter_lower_bound: assert property (@(posedge clock) fifo.counter >= 0);
a_counter_upper_bound: assert property (@(posedge clock) fifo.counter <= 4'd15);

a_full_flag_correct: assert property (@(posedge clock) f_full == (fifo.counter == 4'd15));
a_empty_flag_correct: assert property (@(posedge clock) f_empty == (fifo.counter == 4'd0));

a_data_output_is_from_read_ptr: assert property (@(posedge clock) data_out == fifo.mem[fifo.rd_ptr]);
a_write_data_stored_correctly: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full) |=> fifo.mem[$past(fifo.wr_ptr)] == $past(data_in));

a_cannot_write_when_full: assert property (@(posedge clock) disable iff (reset) (f_full && wr_en) |=> fifo.wr_ptr == $past(fifo.wr_ptr));
a_cannot_read_when_empty: assert property (@(posedge clock) disable iff (reset) (f_empty && rd_en) |=> fifo.rd_ptr == $past(fifo.rd_ptr));

a_simultaneous_ops_hold_counter: assert property (@(posedge clock) disable iff (reset) (wr_en && rd_en && !f_full && !f_empty) |=> fifo.counter == $past(fifo.counter));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
