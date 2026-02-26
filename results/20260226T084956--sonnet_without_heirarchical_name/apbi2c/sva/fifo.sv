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

// Internal signal access via hierarchical references
wire [AWIDTH-1:0] wr_ptr   = fifo_assert_instance.wr_ptr;
wire [AWIDTH-1:0] rd_ptr   = fifo_assert_instance.rd_ptr;
wire [AWIDTH-1:0] counter  = fifo_assert_instance.counter;

	// Internal signal access via hierarchical references would be needed;
	// we use the module's own internal signals by binding into fifo scope.
	// We reference internal registers directly.

	wire [AWIDTH-1:0] wr_ptr_w  = fifo_assert_instance.wr_ptr;  // placeholder - will use bind
	// Use direct signal names since bind gives us access to internals via .*

	// --- Reset assertions ---
	reset_wr_ptr_zero : assert property (
		@(posedge clock) reset |=> (wr_ptr == {AWIDTH{1'b0}})
	);

	reset_rd_ptr_zero : assert property (
		@(posedge clock) reset |=> (rd_ptr == {AWIDTH{1'b0}})
	);

	reset_counter_zero : assert property (
		@(posedge clock) reset |=> (counter == {AWIDTH{1'b0}})
	);

	// --- f_full correctness ---
	f_full_when_counter_15 : assert property (
		@(posedge clock) disable iff (reset)
		(counter == 4'd15) |-> f_full
	);

	not_f_full_when_counter_not_15 : assert property (
		@(posedge clock) disable iff (reset)
		(counter != 4'd15) |-> !f_full
	);

	// --- f_empty correctness ---
	f_empty_when_counter_0 : assert property (
		@(posedge clock) disable iff (reset)
		(counter == 4'd0) |-> f_empty
	);

	not_f_empty_when_counter_not_0 : assert property (
		@(posedge clock) disable iff (reset)
		(counter != 4'd0) |-> !f_empty
	);

	// --- full and empty mutually exclusive ---
	full_and_empty_mutually_exclusive : assert property (
		@(posedge clock) disable iff (reset)
		!(f_full && f_empty)
	);

	// --- Write pointer increments on write when not full ---
	wr_ptr_increments_on_write : assert property (
		@(posedge clock) disable iff (reset)
		(wr_en && !f_full) |=> (wr_ptr == ($past(wr_ptr) + 4'd1))
	);

	// --- Write pointer stable when not writing or full ---
	wr_ptr_stable_when_no_write : assert property (
		@(posedge clock) disable iff (reset)
		(!wr_en || f_full) |=> (wr_ptr == $past(wr_ptr))
	);

	// --- Read pointer increments on read when not empty ---
	rd_ptr_increments_on_read : assert property (
		@(posedge clock) disable iff (reset)
		(rd_en && !f_empty) |=> (rd_ptr == ($past(rd_ptr) + 4'd1))
	);

	// --- Read pointer stable when not reading or empty ---
	rd_ptr_stable_when_no_read : assert property (
		@(posedge clock) disable iff (reset)
		(!rd_en || f_empty) |=> (rd_ptr == $past(rd_ptr))
	);

	// --- Counter increments on write-only ---
	counter_increments_on_write_only : assert property (
		@(posedge clock) disable iff (reset)
		(wr_en && !f_full && !rd_en) |=> (counter == ($past(counter) + 4'd1))
	);

	// --- Counter decrements on read-only ---
	counter_decrements_on_read_only : assert property (
		@(posedge clock) disable iff (reset)
		(rd_en && !f_empty && !wr_en) |=> (counter == ($past(counter) - 4'd1))
	);

	// --- Counter stable on simultaneous read and write (both valid) ---
	counter_stable_on_simultaneous_rw : assert property (
		@(posedge clock) disable iff (reset)
		(wr_en && !f_full && rd_en && !f_empty) |=> (counter == $past(counter))
	);

	// --- Counter stable when no valid read or write ---
	counter_stable_no_op : assert property (
		@(posedge clock) disable iff (reset)
		((!wr_en || f_full) && (!rd_en || f_empty)) |=> (counter == $past(counter))
	);

	// --- No write beyond full ---
	no_wr_ptr_change_when_full : assert property (
		@(posedge clock) disable iff (reset)
		f_full |=> (wr_ptr == $past(wr_ptr))
	);

	// --- No read beyond empty ---
	no_rd_ptr_change_when_empty : assert property (
		@(posedge clock) disable iff (reset)
		f_empty |=> (rd_ptr == $past(rd_ptr))
	);

	// --- Counter never exceeds 15 ---
	counter_never_overflow : assert property (
		@(posedge clock) disable iff (reset)
		counter <= 4'd15
	);

	// --- f_full implies counter at max ---
	f_full_implies_counter_max : assert property (
		@(posedge clock) disable iff (reset)
		f_full |-> (counter == 4'd15)
	);

	// --- f_empty implies counter at zero ---
	f_empty_implies_counter_zero : assert property (
		@(posedge clock) disable iff (reset)
		f_empty |-> (counter == 4'd0)
	);

	// --- After reset deasserts, full and empty flags are in known state ---
	after_reset_empty : assert property (
		@(posedge clock)
		$fell(reset) |=> f_empty
	);

	after_reset_not_full : assert property (
		@(posedge clock)
		$fell(reset) |=> !f_full
	);

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
