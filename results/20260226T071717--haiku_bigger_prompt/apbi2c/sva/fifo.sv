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

full_flag_accurate: assert property (@(posedge clock) disable iff (reset) f_full |-> (fifo.counter == 4'd15));

empty_flag_accurate: assert property (@(posedge clock) disable iff (reset) f_empty |-> (fifo.counter == 4'd0));

full_and_empty_exclusive: assert property (@(posedge clock) disable iff (reset) !(f_full && f_empty));

counter_max_valid: assert property (@(posedge clock) disable iff (reset) (fifo.counter <= 4'd15));

counter_min_valid: assert property (@(posedge clock) disable iff (reset) (fifo.counter >= 4'd0));

write_ptr_increment: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1)));

write_ptr_hold: assert property (@(posedge clock) disable iff (reset) (!wr_en || f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr)));

read_ptr_increment: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1)));

read_ptr_hold: assert property (@(posedge clock) disable iff (reset) (!rd_en || f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr)));

counter_increments_on_write: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter) + 4'd1));

counter_decrements_on_read: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter) - 4'd1));

counter_stable_on_simultaneous: assert property (@(posedge clock) disable iff (reset) (wr_en && rd_en && !f_full && !f_empty) |=> (fifo.counter == $past(fifo.counter)));

counter_stable_on_idle: assert property (@(posedge clock) disable iff (reset) (!wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter)));

data_written_to_memory: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full) |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in)));

data_out_reflects_mem: assert property (@(posedge clock) (data_out == fifo.mem[fifo.rd_ptr]));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
