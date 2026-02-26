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

// Reset assertions
reset_wr_ptr: assert property (@(posedge clock) reset |=> fifo.wr_ptr == {(AWIDTH){1'b0}});
reset_rd_ptr: assert property (@(posedge clock) reset |=> fifo.rd_ptr == {(AWIDTH){1'b0}});
reset_counter: assert property (@(posedge clock) reset |=> fifo.counter == {(AWIDTH){1'b0}});

// f_full and f_empty flag correctness
f_full_when_counter_15: assert property (@(posedge clock) (fifo.counter == 4'd15) |-> f_full);
f_not_full_when_counter_not_15: assert property (@(posedge clock) (fifo.counter != 4'd15) |-> !f_full);
f_empty_when_counter_0: assert property (@(posedge clock) (fifo.counter == 4'd0) |-> f_empty);
f_not_empty_when_counter_not_0: assert property (@(posedge clock) (fifo.counter != 4'd0) |-> !f_empty);

// Mutual exclusion of full and empty
full_and_empty_mutex: assert property (@(posedge clock) !(f_full && f_empty));

// Write pointer behavior
wr_ptr_increments_on_write: assert property (@(posedge clock) disable iff (reset)
    (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1)));

wr_ptr_stable_when_full: assert property (@(posedge clock) disable iff (reset)
    (wr_en && f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr)));

wr_ptr_stable_when_no_write: assert property (@(posedge clock) disable iff (reset)
    (!wr_en) |=> (fifo.wr_ptr == $past(fifo.wr_ptr)));

// Read pointer behavior
rd_ptr_increments_on_read: assert property (@(posedge clock) disable iff (reset)
    (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1)));

rd_ptr_stable_when_empty: assert property (@(posedge clock) disable iff (reset)
    (rd_en && f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr)));

rd_ptr_stable_when_no_read: assert property (@(posedge clock) disable iff (reset)
    (!rd_en) |=> (fifo.rd_ptr == $past(fifo.rd_ptr)));

// Counter behavior: write only
counter_increments_on_write_only: assert property (@(posedge clock) disable iff (reset)
    (wr_en && !f_full && !rd_en) |=> (fifo.counter == ($past(fifo.counter) + 4'd1)));

// Counter behavior: read only
counter_decrements_on_read_only: assert property (@(posedge clock) disable iff (reset)
    (rd_en && !f_empty && !wr_en) |=> (fifo.counter == ($past(fifo.counter) - 4'd1)));

// Counter stable on simultaneous read and write (both enabled, both valid)
counter_stable_on_simultaneous_rw: assert property (@(posedge clock) disable iff (reset)
    (wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter)));

// Counter stable when no valid operation
counter_stable_no_op: assert property (@(posedge clock) disable iff (reset)
    (!wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter)));

// Counter stable when write attempted but full, and no read
counter_stable_write_full_no_read: assert property (@(posedge clock) disable iff (reset)
    (wr_en && f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter)));

// Counter stable when read attempted but empty, and no write
counter_stable_read_empty_no_write: assert property (@(posedge clock) disable iff (reset)
    (rd_en && f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter)));

// Counter never exceeds 15
counter_no_overflow: assert property (@(posedge clock) fifo.counter <= 4'd15);

// data_out reflects mem at rd_ptr
data_out_is_mem_rd_ptr: assert property (@(posedge clock) data_out == fifo.mem[fifo.rd_ptr]);

// Write stores data_in to mem at wr_ptr
write_stores_data: assert property (@(posedge clock) disable iff (reset)
    (wr_en && !f_full) |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in)));

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
