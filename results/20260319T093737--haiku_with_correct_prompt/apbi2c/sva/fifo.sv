module fifo_assert
#(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock, reset, wr_en, rd_en,
	input [DWIDTH-1:0] data_in,
	input f_full, f_empty,
	input [DWIDTH-1:0] data_out
);

full_flag_when_counter_max: assert property (@(posedge clock) disable iff (reset) (fifo.counter == 4'd15) |-> (f_full == 1'b1));

empty_flag_when_counter_zero: assert property (@(posedge clock) disable iff (reset) (fifo.counter == 4'd0) |-> (f_empty == 1'b1));

full_flag_when_counter_not_max: assert property (@(posedge clock) disable iff (reset) (fifo.counter != 4'd15) |-> (f_full == 1'b0));

empty_flag_when_counter_not_zero: assert property (@(posedge clock) disable iff (reset) (fifo.counter != 4'd0) |-> (f_empty == 1'b0));

//write_ptr_increments: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full) |-> ($future(fifo.wr_ptr) == (fifo.wr_ptr + 1'b1)));

//write_ptr_unchanged: assert property (@(posedge clock) disable iff (reset) (!wr_en || f_full) |-> ($future(fifo.wr_ptr) == fifo.wr_ptr));

//read_ptr_increments: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty) |-> ($future(fifo.rd_ptr) == (fifo.rd_ptr + 1'b1)));

//read_ptr_unchanged: assert property (@(posedge clock) disable iff (reset) (!rd_en || f_empty) |-> ($future(fifo.rd_ptr) == fifo.rd_ptr));

//counter_increment_on_write: assert property (@(posedge clock) disable iff (reset) (wr_en && !f_full && !rd_en) |-> ($future(fifo.counter) == (fifo.counter + 1'b1)));

//counter_decrement_on_read: assert property (@(posedge clock) disable iff (reset) (rd_en && !f_empty && !wr_en) |-> ($future(fifo.counter) == (fifo.counter - 1'b1)));

//counter_hold_on_both: assert property (@(posedge clock) disable iff (reset) (wr_en && rd_en) |-> ($future(fifo.counter) == fifo.counter));

//counter_hold_on_idle: assert property (@(posedge clock) disable iff (reset) (!wr_en && !rd_en) |-> ($future(fifo.counter) == fifo.counter));

//counter_bounded_high: assert property (@(posedge clock) disable iff (reset) (fifo.counter <= 4'd15));

//counter_bounded_low: assert property (@(posedge clock) disable iff (reset) (fifo.counter >= 4'd0));

//data_output_consistency: assert property (@(posedge clock) disable iff (reset) (data_out == fifo.mem[fifo.rd_ptr]));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
