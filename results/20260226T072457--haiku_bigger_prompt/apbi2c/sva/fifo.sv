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

full_flag_correct: assert property (@(posedge clock) (f_full == (fifo.counter == 4'd15)));

empty_flag_correct: assert property (@(posedge clock) (f_empty == (fifo.counter == 4'd0)));

wr_ptr_increment_on_write: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 1'b1)));

rd_ptr_increment_on_read: assert property (@(posedge clock) disable iff(reset) (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 1'b1)));

counter_increment_on_write_only: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full && !rd_en) |=> (fifo.counter == ($past(fifo.counter) + 1'b1)));

counter_decrement_on_read_only: assert property (@(posedge clock) disable iff(reset) (rd_en && !f_empty && !wr_en) |=> (fifo.counter == ($past(fifo.counter) - 1'b1)));

counter_stable_simultaneous_rw: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter)));

wr_ptr_stable_when_full: assert property (@(posedge clock) disable iff(reset) (wr_en && f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr)));

rd_ptr_stable_when_empty: assert property (@(posedge clock) disable iff(reset) (rd_en && f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr)));

data_out_equals_mem_at_rd_ptr: assert property (@(posedge clock) (data_out == fifo.mem[fifo.rd_ptr]));

mem_write_on_valid_write: assert property (@(posedge clock) disable iff(reset) (wr_en && !f_full) |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in)));

counter_upper_bound: assert property (@(posedge clock) (fifo.counter <= 4'd15));

wr_ptr_valid_range: assert property (@(posedge clock) (fifo.wr_ptr < (1 << AWIDTH)));

rd_ptr_valid_range: assert property (@(posedge clock) (fifo.rd_ptr < (1 << AWIDTH)));

wr_ptr_zero_after_reset: assert property (@(posedge clock) reset |=> (fifo.wr_ptr == 0));

rd_ptr_zero_after_reset: assert property (@(posedge clock) reset |=> (fifo.rd_ptr == 0));

counter_zero_after_reset: assert property (@(posedge clock) reset |=> (fifo.counter == 0));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
