module fifo_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock,
	input reset,
	input wr_en,
	input rd_en,
	input [DWIDTH-1:0] data_in,
	input f_full,
	input f_empty,
	input [DWIDTH-1:0] data_out
);

	// f_full when counter is 15
	full_flag_correct: assert property (@(posedge clock) (fifo.counter == 4'd15) |-> f_full == 1'b1);

	// not f_full when counter is not 15
	full_flag_deasserted: assert property (@(posedge clock) (fifo.counter != 4'd15) |-> f_full == 1'b0);

	// f_empty when counter is 0
	empty_flag_correct: assert property (@(posedge clock) (fifo.counter == 4'd0) |-> f_empty == 1'b1);

	// not f_empty when counter is not 0
	empty_flag_deasserted: assert property (@(posedge clock) (fifo.counter != 4'd0) |-> f_empty == 1'b0);

	// Cannot be both full and empty simultaneously
	not_full_and_empty: assert property (@(posedge clock) !(f_full && f_empty));

	// On reset, write pointer is 0
	reset_wr_ptr: assert property (@(posedge clock) reset |=> fifo.wr_ptr == {AWIDTH{1'b0}});

	// On reset, read pointer is 0
	reset_rd_ptr: assert property (@(posedge clock) reset |=> fifo.rd_ptr == {AWIDTH{1'b0}});

	// On reset, counter is 0
	reset_counter: assert property (@(posedge clock) reset |=> fifo.counter == {AWIDTH{1'b0}});

	// After reset, FIFO is empty
	reset_empty: assert property (@(posedge clock) reset |=> f_empty == 1'b1);

	// After reset, FIFO is not full
	reset_not_full: assert property (@(posedge clock) reset |=> f_full == 1'b0);

	// Write pointer increments on valid write
	wr_ptr_increment: assert property (@(posedge clock) !reset && wr_en && !f_full |=> fifo.wr_ptr == $past(fifo.wr_ptr) + 1);

	// Write pointer stable when not writing or full
	wr_ptr_stable_no_write: assert property (@(posedge clock) !reset && (!wr_en || f_full) |=> fifo.wr_ptr == $past(fifo.wr_ptr));

	// Read pointer increments on valid read
	rd_ptr_increment: assert property (@(posedge clock) !reset && rd_en && !f_empty |=> fifo.rd_ptr == $past(fifo.rd_ptr) + 1);

	// Read pointer stable when not reading or empty
	rd_ptr_stable_no_read: assert property (@(posedge clock) !reset && (!rd_en || f_empty) |=> fifo.rd_ptr == $past(fifo.rd_ptr));

	// Counter increments on write only (no simultaneous read)
	counter_increment_on_write: assert property (@(posedge clock) !reset && wr_en && !f_full && !rd_en |=> fifo.counter == $past(fifo.counter) + 1);

	// Counter decrements on read only (no simultaneous write)
	counter_decrement_on_read: assert property (@(posedge clock) !reset && rd_en && !f_empty && !wr_en |=> fifo.counter == $past(fifo.counter) - 1);

	// Counter stable on simultaneous read and write (both valid)
	counter_stable_on_rw: assert property (@(posedge clock) !reset && wr_en && !f_full && rd_en && !f_empty |=> fifo.counter == $past(fifo.counter));

	// Counter stable when no read or write
	counter_stable_idle: assert property (@(posedge clock) !reset && !wr_en && !rd_en |=> fifo.counter == $past(fifo.counter));

	// No write when full (write pointer should not change)
	no_write_when_full: assert property (@(posedge clock) !reset && wr_en && f_full |=> fifo.wr_ptr == $past(fifo.wr_ptr));

	// No read when empty (read pointer should not change)
	no_read_when_empty: assert property (@(posedge clock) !reset && rd_en && f_empty |=> fifo.rd_ptr == $past(fifo.rd_ptr));

	// Counter is bounded
	counter_bounded: assert property (@(posedge clock) fifo.counter <= 4'd15);

	// data_out reflects memory at read pointer
	data_out_from_mem: assert property (@(posedge clock) data_out == fifo.mem[fifo.rd_ptr]);

	// Data written to memory correctly on valid write
	data_written_correctly: assert property (@(posedge clock) !reset && wr_en && !f_full |=> fifo.mem[$past(fifo.wr_ptr)] == $past(data_in));

	// Counter should not change when write to full or read from empty without other operation
	counter_stable_write_full: assert property (@(posedge clock) !reset && wr_en && f_full && !rd_en |=> fifo.counter == $past(fifo.counter));

	// Counter should not change when read from empty without write
	counter_stable_read_empty: assert property (@(posedge clock) !reset && rd_en && f_empty && !wr_en |=> fifo.counter == $past(fifo.counter));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
