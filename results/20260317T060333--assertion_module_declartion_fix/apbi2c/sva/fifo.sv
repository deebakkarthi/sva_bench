module fifo_assert
#(
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

// After reset, wr_ptr must be 0
reset_wr_ptr_zero: assert property (
    @(posedge clock) (reset) |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
);

// After reset, rd_ptr must be 0
reset_rd_ptr_zero: assert property (
    @(posedge clock) (reset) |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
);

// After reset, counter must be 0
reset_counter_zero: assert property (
    @(posedge clock) (reset) |=> (fifo.counter == {(AWIDTH){1'b0}})
);

// After reset, f_empty must be asserted
reset_f_empty_high: assert property (
    @(posedge clock) (reset) |=> (f_empty == 1'b1)
);

// After reset, f_full must be deasserted
reset_f_full_low: assert property (
    @(posedge clock) (reset) |=> (f_full == 1'b0)
);

// f_full is asserted iff counter == 15
f_full_when_counter_15: assert property (
    @(posedge clock) disable iff (reset)
    (fifo.counter == 4'd15) |-> (f_full == 1'b1)
);

f_full_only_when_counter_15: assert property (
    @(posedge clock) disable iff (reset)
    (f_full == 1'b1) |-> (fifo.counter == 4'd15)
);

// f_empty is asserted iff counter == 0
f_empty_when_counter_0: assert property (
    @(posedge clock) disable iff (reset)
    (fifo.counter == 4'd0) |-> (f_empty == 1'b1)
);

f_empty_only_when_counter_0: assert property (
    @(posedge clock) disable iff (reset)
    (f_empty == 1'b1) |-> (fifo.counter == 4'd0)
);

// f_full and f_empty cannot be simultaneously asserted
full_and_empty_mutex: assert property (
    @(posedge clock) disable iff (reset)
    not (f_full && f_empty)
);

// Write pointer increments when wr_en and not full and no reset
wr_ptr_increments_on_write: assert property (
    @(posedge clock) disable iff (reset)
    (wr_en && !f_full && !reset) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1))
);

// Write pointer stable when full or wr_en deasserted
wr_ptr_stable_when_full: assert property (
    @(posedge clock) disable iff (reset)
    (!wr_en && !reset) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
);

wr_ptr_stable_on_full: assert property (
    @(posedge clock) disable iff (reset)
    (f_full && !reset) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
);

// Read pointer increments when rd_en and not empty
rd_ptr_increments_on_read: assert property (
    @(posedge clock) disable iff (reset)
    (rd_en && !f_empty && !reset) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1))
);

// Read pointer stable when empty or rd_en deasserted
rd_ptr_stable_when_empty: assert property (
    @(posedge clock) disable iff (reset)
    (f_empty && !reset) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
);

rd_ptr_stable_when_no_rd_en: assert property (
    @(posedge clock) disable iff (reset)
    (!rd_en && !reset) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
);

// Counter increments on write-only (not full, not simultaneous read)
counter_increments_on_write_only: assert property (
    @(posedge clock) disable iff (reset)
    (wr_en && !f_full && !rd_en && !reset) |=> (fifo.counter == ($past(fifo.counter) + 4'd1))
);

// Counter decrements on read-only (not empty, not simultaneous write)
counter_decrements_on_read_only: assert property (
    @(posedge clock) disable iff (reset)
    (rd_en && !f_empty && !wr_en && !reset) |=> (fifo.counter == ($past(fifo.counter) - 4'd1))
);

// Counter stable when both read and write happen simultaneously
counter_stable_on_simultaneous_rw: assert property (
    @(posedge clock) disable iff (reset)
    (wr_en && !f_full && rd_en && !f_empty && !reset) |=> (fifo.counter == $past(fifo.counter))
);

// Counter stable when neither read nor write
counter_stable_when_idle: assert property (
    @(posedge clock) disable iff (reset)
    (!wr_en && !rd_en && !reset) |=> (fifo.counter == $past(fifo.counter))
);

// Counter never exceeds 15
counter_never_overflow: assert property (
    @(posedge clock) disable iff (reset)
    (fifo.counter <= 4'd15)
);

// data_out equals mem[rd_ptr]
data_out_equals_mem_rd_ptr: assert property (
    @(posedge clock) disable iff (reset)
    (data_out == fifo.mem[fifo.rd_ptr])
);

// When full, writing does not change counter
counter_stable_when_full_write: assert property (
    @(posedge clock) disable iff (reset)
    (wr_en && f_full && !rd_en && !reset) |=> (fifo.counter == $past(fifo.counter))
);

// When empty, reading does not change counter
counter_stable_when_empty_read: assert property (
    @(posedge clock) disable iff (reset)
    (rd_en && f_empty && !wr_en && !reset) |=> (fifo.counter == $past(fifo.counter))
);

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
