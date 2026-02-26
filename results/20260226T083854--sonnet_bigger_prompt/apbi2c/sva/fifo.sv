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

    // Reset: wr_ptr cleared synchronously
    reset_clears_wr_ptr: assert property (
        @(posedge clock) reset |=> fifo.wr_ptr == {AWIDTH{1'b0}}
    );

    // Reset: rd_ptr cleared synchronously
    reset_clears_rd_ptr: assert property (
        @(posedge clock) reset |=> fifo.rd_ptr == {AWIDTH{1'b0}}
    );

    // Reset: counter cleared synchronously
    reset_clears_counter: assert property (
        @(posedge clock) reset |=> fifo.counter == {AWIDTH{1'b0}}
    );

    // f_full asserts iff counter == 15
    f_full_iff_counter_max: assert property (
        @(posedge clock) f_full == (fifo.counter == 4'd15)
    );

    // f_empty asserts iff counter == 0
    f_empty_iff_counter_zero: assert property (
        @(posedge clock) f_empty == (fifo.counter == 4'd0)
    );

    // f_full and f_empty are mutually exclusive
    full_and_empty_mutex: assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // Counter stays within valid range [0, 15]
    counter_upper_bound: assert property (
        @(posedge clock) fifo.counter <= 4'd15
    );

    // Write pointer increments on valid write
    wr_ptr_increments_on_valid_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> fifo.wr_ptr == ($past(fifo.wr_ptr) + 1'b1)
    );

    // Write pointer stable when no valid write
    wr_ptr_stable_when_no_write: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=> fifo.wr_ptr == $past(fifo.wr_ptr)
    );

    // Read pointer increments on valid read
    rd_ptr_increments_on_valid_read: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=> fifo.rd_ptr == ($past(fifo.rd_ptr) + 1'b1)
    );

    // Read pointer stable when no valid read
    rd_ptr_stable_when_no_read: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=> fifo.rd_ptr == $past(fifo.rd_ptr)
    );

    // Counter increments on write-only (no concurrent read)
    counter_increments_on_write_only: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=> fifo.counter == ($past(fifo.counter) + 1'b1)
    );

    // Counter decrements on read-only (no concurrent write)
    counter_decrements_on_read_only: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=> fifo.counter == ($past(fifo.counter) - 1'b1)
    );

    // Counter stable when both wr_en and rd_en asserted simultaneously
    counter_stable_on_simultaneous_rw: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && rd_en) |=> fifo.counter == $past(fifo.counter)
    );

    // Counter stable when neither wr_en nor rd_en
    counter_stable_on_no_activity: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=> fifo.counter == $past(fifo.counter)
    );

    // Counter stable when write attempted on full FIFO (no read)
    counter_stable_on_full_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full && !rd_en) |=> fifo.counter == $past(fifo.counter)
    );

    // Counter stable when read attempted on empty FIFO (no write)
    counter_stable_on_empty_read: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty && !wr_en) |=> fifo.counter == $past(fifo.counter)
    );

    // data_out always reflects mem at current rd_ptr
    data_out_tracks_mem_rd_ptr: assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    // Memory written correctly on valid write
    mem_written_on_valid_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> fifo.mem[$past(fifo.wr_ptr)] == $past(data_in)
    );

    // f_full cannot assert immediately after reset
    no_full_after_reset: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // f_empty must assert immediately after reset
    empty_after_reset: assert property (
        @(posedge clock) reset |=> f_empty
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
