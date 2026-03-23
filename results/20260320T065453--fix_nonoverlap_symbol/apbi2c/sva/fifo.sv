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

    // f_full is asserted when counter == 15
    f_full_when_counter_15: assert property (
        @(posedge clock) (fifo.counter == 4'd15) |-> f_full
    );

    // f_full is deasserted when counter != 15
    f_full_deasserted_when_counter_not_15: assert property (
        @(posedge clock) (fifo.counter != 4'd15) |-> !f_full
    );

    // f_empty is asserted when counter == 0
    f_empty_when_counter_zero: assert property (
        @(posedge clock) (fifo.counter == 4'd0) |-> f_empty
    );

    // f_empty is deasserted when counter != 0
    f_empty_deasserted_when_counter_not_zero: assert property (
        @(posedge clock) (fifo.counter != 4'd0) |-> !f_empty
    );

    // f_full and f_empty cannot be asserted simultaneously
    full_and_empty_mutually_exclusive: assert property (
        @(posedge clock) f_full |-> !f_empty
    );

    // f_empty and f_full cannot be asserted simultaneously
    empty_and_full_mutually_exclusive: assert property (
        @(posedge clock) f_empty |-> !f_full
    );

    // data_out always equals mem[rd_ptr]
    data_out_equals_mem_at_rd_ptr: assert property (
        @(posedge clock) 1'b1 |-> (data_out === fifo.mem[fifo.rd_ptr])
    );

    // After reset: wr_ptr is 0
    reset_wr_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    // After reset: rd_ptr is 0
    reset_rd_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    // After reset: counter is 0
    reset_counter_zero: assert property (
        @(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    // After reset: f_empty is asserted
    reset_f_empty_asserted: assert property (
        @(posedge clock) reset |=> f_empty
    );

    // After reset: f_full is deasserted
    reset_f_full_deasserted: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // Write when enabled and not full: wr_ptr increments by 1
    wr_ptr_increments_on_write: assert property (
        @(posedge clock) (!reset && wr_en && !f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr) + 1'b1)
    );

    // No write when full: wr_ptr stays the same
    wr_ptr_stable_when_full: assert property (
        @(posedge clock) (!reset && f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // No write when wr_en deasserted: wr_ptr stays the same
    wr_ptr_stable_when_wr_en_low: assert property (
        @(posedge clock) (!reset && !wr_en) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read when enabled and not empty: rd_ptr increments by 1
    rd_ptr_increments_on_read: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr) + 1'b1)
    );

    // No read when empty: rd_ptr stays the same
    rd_ptr_stable_when_empty: assert property (
        @(posedge clock) (!reset && f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // No read when rd_en deasserted: rd_ptr stays the same
    rd_ptr_stable_when_rd_en_low: assert property (
        @(posedge clock) (!reset && !rd_en) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter increments on write-only (wr_en && !f_full && !rd_en)
    counter_increments_on_write_only: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter) + 1'b1)
    );

    // Counter decrements on read-only (rd_en && !f_empty && !wr_en)
    counter_decrements_on_read_only: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter) - 1'b1)
    );

    // Counter stays same on simultaneous read and write (both valid)
    counter_stable_on_simultaneous_rw: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stays same when neither read nor write active
    counter_stable_when_idle: assert property (
        @(posedge clock) (!reset && !wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stable when write attempted on full FIFO (no valid read)
    counter_stable_on_write_to_full: assert property (
        @(posedge clock) (!reset && wr_en && f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stable when read attempted on empty FIFO (no valid write)
    counter_stable_on_read_from_empty: assert property (
        @(posedge clock) (!reset && rd_en && f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // counter never exceeds 15 (depth - 1)
    counter_never_exceeds_max: assert property (
        @(posedge clock) 1'b1 |-> (fifo.counter <= 4'd15)
    );

    // When f_full, writing is blocked (wr_ptr does not advance)
    write_blocked_when_full: assert property (
        @(posedge clock) (!reset && f_full && !rd_en) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // When f_empty, reading is blocked (rd_ptr does not advance)
    read_blocked_when_empty: assert property (
        @(posedge clock) (!reset && f_empty && !wr_en) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Write then read: written data appears at data_out after rd_ptr advances
    write_data_stored_correctly: assert property (
        @(posedge clock) (!reset && wr_en && !f_full) |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
