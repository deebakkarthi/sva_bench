module fifo_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock, reset, wr_en, rd_en,
	input [DWIDTH-1:0] data_in,
	output f_full, f_empty,
	output [DWIDTH-1:0] data_out
);

a_reset_sets_empty: assert property (@(posedge clock) reset |-> ##1 f_empty);

a_reset_clears_full: assert property (@(posedge clock) reset |-> ##1 !f_full);

a_full_when_counter_max: assert property (@(posedge clock) (counter == 4'd15) |-> f_full);

a_not_full_when_below_max: assert property (@(posedge clock) (counter < 4'd15) |-> !f_full);

a_empty_when_counter_zero: assert property (@(posedge clock) (counter == 4'd0) |-> f_empty);

a_not_empty_when_above_zero: assert property (@(posedge clock) (counter > 4'd0) |-> !f_empty);

a_wr_pointer_increment_on_write: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full) |=> wr_ptr == ($past(wr_ptr) + 1));

a_wr_pointer_hold_when_full_or_disabled: assert property (@(posedge clock) disable iff(reset) (!wr_en || f_full) |=> wr_ptr == $past(wr_ptr));

a_rd_pointer_increment_on_read: assert property (@(posedge clock) disable iff(reset) (rd_en && !f_empty) |=> rd_ptr == ($past(rd_ptr) + 1));

a_rd_pointer_hold_when_empty_or_disabled: assert property (@(posedge clock) disable iff(reset) (!rd_en || f_empty) |=> rd_ptr == $past(rd_ptr));

a_counter_increment_on_write_only: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full && !rd_en) |=> counter == ($past(counter) + 1));

a_counter_decrement_on_read_only: assert property (@(posedge clock) disable iff(reset) (rd_en && !f_empty && !wr_en) |=> counter == ($past(counter) - 1));

a_counter_unchanged_on_simultaneous_rw: assert property (@(posedge clock) disable iff(reset) (wr_en && rd_en) |=> counter == $past(counter));

a_counter_unchanged_when_idle: assert property (@(posedge clock) disable iff(reset) (!wr_en && !rd_en) |=> counter == $past(counter));

a_counter_never_exceeds_max: assert property (@(posedge clock) counter <= 4'd15);

a_counter_never_negative: assert property (@(posedge clock) counter >= 4'd0);

a_never_both_full_and_empty: assert property (@(posedge clock) !(f_full && f_empty));

a_wr_pointer_in_range: assert property (@(posedge clock) (wr_ptr >= 4'd0) && (wr_ptr <= 4'd15));

a_rd_pointer_in_range: assert property (@(posedge clock) (rd_ptr >= 4'd0) && (rd_ptr <= 4'd15));

a_data_out_reflects_read_address: assert property (@(posedge clock) data_out == mem[rd_ptr]);

a_no_write_when_full: assert property (@(posedge clock) disable iff(reset) f_full && wr_en |-> ##1 wr_ptr == $past(wr_ptr));

a_no_read_when_empty: assert property (@(posedge clock) disable iff(reset) f_empty && rd_en |-> ##1 rd_ptr == $past(rd_ptr));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
