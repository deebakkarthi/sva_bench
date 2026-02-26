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

	reset_clears_wr_ptr: assert property (
		@(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
	);

	reset_clears_rd_ptr: assert property (
		@(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
	);

	reset_clears_counter: assert property (
		@(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
	);

	empty_flag_asserts_at_zero_count: assert property (
		@(posedge clock) disable iff(reset) (fifo.counter == 4'd0) |-> (f_empty == 1'b1)
	);

	empty_flag_deasserts_above_zero: assert property (
		@(posedge clock) disable iff(reset) (fifo.counter != 4'd0) |-> (f_empty == 1'b0)
	);

	full_flag_asserts_at_max_count: assert property (
		@(posedge clock) disable iff(reset) (fifo.counter == 4'd15) |-> (f_full == 1'b1)
	);

	full_flag_deasserts_below_max: assert property (
		@(posedge clock) disable iff(reset) (fifo.counter != 4'd15) |-> (f_full == 1'b0)
	);

	wr_ptr_increments_on_valid_write: assert property (
		@(posedge clock) disable iff(reset) (wr_en && !f_full) |=> 
			(fifo.wr_ptr == $past(fifo.wr_ptr, 1) + 4'd1)
	);

	wr_ptr_unchanged_without_write_enable: assert property (
		@(posedge clock) disable iff(reset) !wr_en |=> 
			(fifo.wr_ptr == $past(fifo.wr_ptr, 1))
	);

	wr_ptr_unchanged_when_full: assert property (
		@(posedge clock) disable iff(reset) (wr_en && f_full) |=> 
			(fifo.wr_ptr == $past(fifo.wr_ptr, 1))
	);

	rd_ptr_increments_on_valid_read: assert property (
		@(posedge clock) disable iff(reset) (rd_en && !f_empty) |=> 
			(fifo.rd_ptr == $past(fifo.rd_ptr, 1) + 4'd1)
	);

	rd_ptr_unchanged_without_read_enable: assert property (
		@(posedge clock) disable iff(reset) !rd_en |=> 
			(fifo.rd_ptr == $past(fifo.rd_ptr, 1))
	);

	rd_ptr_unchanged_when_empty: assert property (
		@(posedge clock) disable iff(reset) (rd_en && f_empty) |=> 
			(fifo.rd_ptr == $past(fifo.rd_ptr, 1))
	);

	counter_increments_on_write_only: assert property (
		@(posedge clock) disable iff(reset) (wr_en && !f_full && !rd_en) |=> 
			(fifo.counter == $past(fifo.counter, 1) + 4'd1)
	);

	counter_decrements_on_read_only: assert property (
		@(posedge clock) disable iff(reset) (rd_en && !f_empty && !wr_en) |=> 
			(fifo.counter == $past(fifo.counter, 1) - 4'd1)
	);

	counter_unchanged_on_simultaneous_read_write: assert property (
		@(posedge clock) disable iff(reset) (wr_en && rd_en) |=> 
			(fifo.counter == $past(fifo.counter, 1))
	);

	counter_unchanged_on_no_activity: assert property (
		@(posedge clock) disable iff(reset) (!wr_en && !rd_en) |=> 
			(fifo.counter == $past(fifo.counter, 1))
	);

	data_written_to_memory_at_write_ptr: assert property (
		@(posedge clock) disable iff(reset) (wr_en && !f_full) |=> 
			(fifo.mem[$past(fifo.wr_ptr, 1)] == $past(data_in, 1))
	);

	data_out_reflects_read_pointer_address: assert property (
		@(posedge clock) disable iff(reset) 1'b1 |-> 
			(data_out == fifo.mem[fifo.rd_ptr])
	);

	wr_ptr_wraps_at_depth: assert property (
		@(posedge clock) disable iff(reset) 
			($past(fifo.wr_ptr, 1) == 4'd15 && wr_en && !f_full) |=> 
			(fifo.wr_ptr == 4'd0)
	);

	rd_ptr_wraps_at_depth: assert property (
		@(posedge clock) disable iff(reset) 
			($past(fifo.rd_ptr, 1) == 4'd15 && rd_en && !f_empty) |=> 
			(fifo.rd_ptr == 4'd0)
	);

	full_and_empty_mutually_exclusive: assert property (
		@(posedge clock) disable iff(reset) !(f_full && f_empty)
	);

	counter_within_valid_range: assert property (
		@(posedge clock) disable iff(reset) 
			(fifo.counter >= 4'd0 && fifo.counter <= 4'd15)
	);

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
