module fifo_assert #(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 4
)(
    input clock,
    input reset,
    input wr_en,
    input rd_en,
    input [DWIDTH-1:0] data_in,
    input f_full,
    input f_empty,
    input [DWIDTH-1:0] data_out
);

// f_full correctness
f_full_when_counter_max : assert property (
    @(posedge clock)
    (fifo.counter == 4'd15) |-> (f_full == 1'b1)
);

f_full_only_when_counter_max : assert property (
    @(posedge clock)
    (f_full == 1'b1) |-> (fifo.counter == 4'd15)
);

// f_empty correctness
f_empty_when_counter_zero : assert property (
    @(posedge clock)
    (fifo.counter == 4'd0) |-> (f_empty == 1'b1)
);

f_empty_only_when_counter_zero : assert property (
    @(posedge clock)
    (f_empty == 1'b1) |-> (fifo.counter == 4'd0)
);

// f_full and f_empty are mutually exclusive
full_and_empty_mutex : assert property (
    @(posedge clock)
    !(f_full && f_empty)
);

// Reset: write pointer clears to 0
reset_clears_wr_ptr : assert property (
    @(posedge clock)
    (reset) |=> (fifo.wr_ptr == {AWIDTH{1'b0}})
);

// Reset: read pointer clears to 0
reset_clears_rd_ptr : assert property (
    @(posedge clock)
    (reset) |=> (fifo.rd_ptr == {AWIDTH{1'b0}})
);

// Reset: counter clears to 0
reset_clears_counter : assert property (
    @(posedge clock)
    (reset) |=> (fifo.counter == {AWIDTH{1'b0}})
);

// Write pointer increments on a valid write
wr_ptr_increments_on_valid_write : assert property (
    @(posedge clock)
    (!reset && wr_en && !f_full)
    |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
);

// Write pointer holds when no valid write
wr_ptr_holds_when_no_write : assert property (
    @(posedge clock)
    (!reset && !(wr_en && !f_full))
    |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
);

// Read pointer increments on a valid read
rd_ptr_increments_on_valid_read : assert property (
    @(posedge clock)
    (!reset && rd_en && !f_empty)
    |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
);

// Read pointer holds when no valid read
rd_ptr_holds_when_no_read : assert property (
    @(posedge clock)
    (!reset && !(rd_en && !f_empty))
    |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
);

// Counter increments on write-only
counter_increments_on_write_only : assert property (
    @(posedge clock)
    (!reset && wr_en && !f_full && !rd_en)
    |=> (fifo.counter == ($past(fifo.counter) + {{(AWIDTH-1){1'b0}}, 1'b1}))
);

// Counter decrements on read-only
counter_decrements_on_read_only : assert property (
    @(posedge clock)
    (!reset && rd_en && !f_empty && !wr_en)
    |=> (fifo.counter == ($past(fifo.counter) - {{(AWIDTH-1){1'b0}}, 1'b1}))
);

// Counter stable on simultaneous valid read and valid write
counter_stable_on_simultaneous_rw : assert property (
    @(posedge clock)
    (!reset && rd_en && !f_empty && wr_en && !f_full)
    |=> (fifo.counter == $past(fifo.counter))
);

// Counter stable when idle
counter_stable_when_idle : assert property (
    @(posedge clock)
    (!reset && !wr_en && !rd_en)
    |=> (fifo.counter == $past(fifo.counter))
);

// Counter does not change when write attempted on full FIFO (no simultaneous read)
counter_stable_write_when_full : assert property (
    @(posedge clock)
    (!reset && wr_en && f_full && !rd_en)
    |=> (fifo.counter == $past(fifo.counter))
);

// Counter does not change when read attempted on empty FIFO (no simultaneous write)
counter_stable_read_when_empty : assert property (
    @(posedge clock)
    (!reset && rd_en && f_empty && !wr_en)
    |=> (fifo.counter == $past(fifo.counter))
);

// Write pointer does not advance when FIFO is full
wr_ptr_holds_when_full : assert property (
    @(posedge clock)
    (!reset && wr_en && f_full)
    |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
);

// Read pointer does not advance when FIFO is empty
rd_ptr_holds_when_empty : assert property (
    @(posedge clock)
    (!reset && rd_en && f_empty)
    |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
);

// Counter stays within valid range [0, 15]
counter_within_bounds : assert property (
    @(posedge clock)
    (fifo.counter <= 4'd15)
);

// data_out always reflects mem at rd_ptr
data_out_reflects_mem_at_rd_ptr : assert property (
    @(posedge clock)
    (data_out == fifo.mem[fifo.rd_ptr])
);

// After a valid write, mem at previous wr_ptr contains data_in
mem_written_on_valid_write : assert property (
    @(posedge clock)
    (!reset && wr_en && !f_full)
    |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
);

// FIFO becomes non-empty after a valid write into empty FIFO
fifo_non_empty_after_write_into_empty : assert property (
    @(posedge clock)
    (!reset && wr_en && f_empty && !rd_en)
    |=> (!f_empty)
);

// FIFO becomes non-full after a valid read from full FIFO
fifo_non_full_after_read_from_full : assert property (
    @(posedge clock)
    (!reset && rd_en && f_full && !wr_en)
    |=> (!f_full)
);

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
