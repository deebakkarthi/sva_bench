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


// Reset assertions
reset_clears_wr_ptr : assert property (@(posedge clock) reset |=> (wr_ptr == 0))
else $error("wr_ptr not cleared on reset");

reset_clears_rd_ptr : assert property (@(posedge clock) reset |=> (rd_ptr == 0))
		else $error("rd_ptr not cleared on reset");

		reset_clears_counter : assert property (@(posedge clock) reset |=> (counter == 0))
	else $error("counter not cleared on reset");

	// Full/empty flag correctness
f_full_when_counter_15 : assert property (@(posedge clock) (counter == 4'd15) |-> f_full)
else $error("f_full should be high when counter == 15");

f_full_only_when_counter_15 : assert property (@(posedge clock) f_full |-> (counter == 4'd15))
		else $error("f_full should only be high when counter == 15");

		f_empty_when_counter_0 : assert property (@(posedge clock) (counter == 4'd0) |-> f_empty)
	else $error("f_empty should be high when counter == 0");

	f_empty_only_when_counter_0 : assert property (@(posedge clock) f_empty |-> (counter == 4'd0))
else $error("f_empty should only be high when counter == 0");

full_and_empty_mutually_exclusive : assert property (@(posedge clock) !(f_full && f_empty))
		else $error("f_full and f_empty cannot both be asserted simultaneously");

		// Write pointer behavior
	wr_ptr_increments_on_write : assert property (@(posedge clock)
	(!reset && wr_en && !f_full) |=> (wr_ptr == $past(wr_ptr) + 1'b1))
	else $error("wr_ptr should increment on write when not full");

	wr_ptr_stable_when_full : assert property (@(posedge clock)
(!reset && wr_en && f_full) |=> (wr_ptr == $past(wr_ptr)))
else $error("wr_ptr should not change when FIFO is full");

wr_ptr_stable_when_no_write : assert property (@(posedge clock)
		(!reset && !wr_en) |=> (wr_ptr == $past(wr_ptr)))
		else $error("wr_ptr should not change when wr_en is deasserted");

		// Read pointer behavior
	rd_ptr_increments_on_read : assert property (@(posedge clock)
	(!reset && rd_en && !f_empty) |=> (rd_ptr == $past(rd_ptr) + 1'b1))
	else $error("rd_ptr should increment on read when not empty");

	rd_ptr_stable_when_empty : assert property (@(posedge clock)
(!reset && rd_en && f_empty) |=> (rd_ptr == $past(rd_ptr)))
else $error("rd_ptr should not change when FIFO is empty");

rd_ptr_stable_when_no_read : assert property (@(posedge clock)
		(!reset && !rd_en) |=> (rd_ptr == $past(rd_ptr)))
		else $error("rd_ptr should not change when rd_en is deasserted");

		// Counter behavior
	counter_increments_on_write_only : assert property (@(posedge clock)
	(!reset && wr_en && !f_full && !rd_en) |=> (counter == $past(counter) + 1'b1))
	else $error("counter should increment on write-only");

	counter_decrements_on_read_only : assert property (@(posedge clock)
(!reset && rd_en && !f_empty && !wr_en) |=> (counter == $past(counter) - 1'b1))
else $error("counter should decrement on read-only");

counter_stable_on_simultaneous_rw : assert property (@(posedge clock)
		(!reset && wr_en && !f_full && rd_en && !f_empty) |=> (counter == $past(counter)))
		else $error("counter should remain stable on simultaneous read and write");

		counter_stable_when_idle : assert property (@(posedge clock)
	(!reset && !wr_en && !rd_en) |=> (counter == $past(counter)))
	else $error("counter should remain stable when neither read nor write");

	counter_stable_when_full_write : assert property (@(posedge clock)
(!reset && wr_en && f_full && !rd_en) |=> (counter == $past(counter)))
else $error("counter should not change on write to full FIFO");

counter_stable_when_empty_read : assert property (@(posedge clock)
		(!reset && rd_en && f_empty && !wr_en) |=> (counter == $past(counter)))
		else $error("counter should not change on read from empty FIFO");

		// Counter bounds
	counter_never_exceeds_max : assert property (@(posedge clock) counter <= 4'd15)
	else $error("counter should never exceed 15");

	// No overflow: writing to full FIFO does not corrupt write pointer
no_wr_ptr_change_when_full : assert property (@(posedge clock)
(f_full && wr_en && !rd_en) |=> (wr_ptr == $past(wr_ptr)))
else $error("wr_ptr must not change when FIFO is full");

// No underflow: reading from empty FIFO does not corrupt read pointer
	no_rd_ptr_change_when_empty : assert property (@(posedge clock)
	(f_empty && rd_en && !wr_en) |=> (rd_ptr == $past(rd_ptr)))
	else $error("rd_ptr must not change when FIFO is empty");

	endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
