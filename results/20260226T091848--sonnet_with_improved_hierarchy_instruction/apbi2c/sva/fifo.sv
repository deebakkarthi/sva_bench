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

    // After reset, write pointer should be 0
    reset_wr_ptr: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    // After reset, read pointer should be 0
    reset_rd_ptr: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    // After reset, counter should be 0
    reset_counter: assert property (
        @(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    // f_full is asserted iff counter == 15
    f_full_condition: assert property (
        @(posedge clock) f_full == (fifo.counter == 4'd15)
    );

    // f_empty is asserted iff counter == 0
    f_empty_condition: assert property (
        @(posedge clock) f_empty == (fifo.counter == 4'd0)
    );

    // f_full and f_empty cannot be simultaneously asserted
    full_and_empty_mutex: assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // Counter should not exceed 15
    counter_no_overflow: assert property (
        @(posedge clock) fifo.counter <= 4'd15
    );

    // Write pointer increments on valid write
    wr_ptr_increment: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1))
    );

    // Write pointer stays same when not writing or fifo is full
    wr_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer increments on valid read
    rd_ptr_increment: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1))
    );

    // Read pointer stays same when not reading or fifo is empty
    rd_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter increments when writing only (not reading) and not full
    counter_increment_on_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !rd_en && !f_full) |=> (fifo.counter == ($past(fifo.counter) + 4'd1))
    );

    // Counter decrements when reading only (not writing) and not empty
    counter_decrement_on_read: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !wr_en && !f_empty) |=> (fifo.counter == ($past(fifo.counter) - 4'd1))
    );

    // Counter stays same on simultaneous read and write (both valid)
    counter_stable_on_simultaneous_rw: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && rd_en && !f_full && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stays same when no read or write
    counter_stable_on_no_rw: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // No write when full - write pointer should not change
    no_write_when_full: assert property (
        @(posedge clock) disable iff (reset)
        (f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // No read when empty - read pointer should not change
    no_read_when_empty: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter should not underflow - reading when empty should keep counter at 0
    counter_no_underflow: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && rd_en && !wr_en) |=> (fifo.counter == 4'd0)
    );

    // Counter should not overflow - writing when full should keep counter at 15
    counter_no_overflow_full: assert property (
        @(posedge clock) disable iff (reset)
        (f_full && wr_en && !rd_en) |=> (fifo.counter == 4'd15)
    );

    // data_out reflects mem at rd_ptr
    data_out_reflects_mem: assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance
(.*);
