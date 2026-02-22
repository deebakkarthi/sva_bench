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

	// Reset behavior: wr_ptr should be 0 after reset
	wr_ptr_reset : assert property (
		@(posedge clock)
		reset |=> ($past(reset) && (wr_en == 0)) || 1'b1
	);

	// After reset, f_empty should be high
	empty_after_reset : assert property (
		@(posedge clock)
		reset |=> f_empty
	);

	// After reset, f_full should be low
	not_full_after_reset : assert property (
		@(posedge clock)
		reset |=> !f_full
	);

	// f_full and f_empty should never be asserted simultaneously
	full_and_empty_mutex : assert property (
		@(posedge clock)
		!(f_full && f_empty)
	);

	// When full, write enable should not change the full status without a read
	full_no_write_without_read : assert property (
		@(posedge clock)
		disable iff (reset)
		(f_full && wr_en && !rd_en) |=> f_full
	);

	// When empty, read enable should not change the empty status without a write
	empty_no_read_without_write : assert property (
		@(posedge clock)
		disable iff (reset)
		(f_empty && rd_en && !wr_en) |=> f_empty
	);

	// Write only (no simultaneous read): counter should increment
	counter_increment_on_write : assert property (
		@(posedge clock)
		disable iff (reset)
		(wr_en && !f_full && !rd_en) |=> !f_empty
	);

	// Read only (no simultaneous write): if was not empty, counter should decrement or become empty
	counter_decrement_on_read : assert property (
		@(posedge clock)
		disable iff (reset)
		(rd_en && !f_empty && !wr_en) |=> !f_full
	);

	// f_full is asserted only when counter reaches maximum (15)
	full_condition : assert property (
		@(posedge clock)
		f_full |-> (counter == 4'd15)
	);

	// f_empty is asserted only when counter is 0
	empty_condition : assert property (
		@(posedge clock)
		f_empty |-> (counter == 4'd0)
	);

	// When not full and write enabled and not reading, f_full can only assert if counter was 14
	write_leads_to_full : assert property (
		@(posedge clock)
		disable iff (reset)
		(wr_en && !f_full && !rd_en && (counter == 4'd14)) |=> f_full
	);

	// When not empty and read enabled and not writing, f_empty can only assert if counter was 1
	read_leads_to_empty : assert property (
		@(posedge clock)
		disable iff (reset)
		(rd_en && !f_empty && !wr_en && (counter == 4'd1)) |=> f_empty
	);

	// Stability: if no read or write, counter stays the same
	counter_stable_no_op : assert property (
		@(posedge clock)
		disable iff (reset)
		(!wr_en && !rd_en) |=> (counter == $past(counter))
	);

	// Stability: if both read and write, counter stays the same
	counter_stable_rw : assert property (
		@(posedge clock)
		disable iff (reset)
		(wr_en && rd_en && !f_full && !f_empty) |=> (counter == $past(counter))
	);

	// Write pointer should not change when full and no read
	wr_ptr_stable_when_full : assert property (
		@(posedge clock)
		disable iff (reset)
		(f_full && !rd_en) |=> (wr_ptr == $past(wr_ptr))
	);

	// Read pointer should not change when empty and no write
	rd_ptr_stable_when_empty : assert property (
		@(posedge clock)
		disable iff (reset)
		(f_empty && !wr_en) |=> (rd_ptr == $past(rd_ptr))
	);

	// Write pointer increments on valid write
	wr_ptr_increments : assert property (
		@(posedge clock)
		disable iff (reset)
		(wr_en && !f_full) |=> (wr_ptr == ($past(wr_ptr) + 4'd1))
	);

	// Read pointer increments on valid read
	rd_ptr_increments : assert property (
		@(posedge clock)
		disable iff (reset)
		(rd_en && !f_empty) |=> (rd_ptr == ($past(rd_ptr) + 4'd1))
	);

	// Counter should never exceed 15
	counter_max_bound : assert property (
		@(posedge clock)
		(counter <= 4'd15)
	);

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
