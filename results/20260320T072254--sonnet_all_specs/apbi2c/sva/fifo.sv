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

    // -------------------------------------------------------------------------
    // f_full and f_empty assignments
    // -------------------------------------------------------------------------

    f_full_when_counter_15 : assert property (
        @(posedge clock)
        (fifo.counter == 4'd15) |-> f_full
    );

    f_full_only_when_counter_15 : assert property (
        @(posedge clock)
        f_full |-> (fifo.counter == 4'd15)
    );

    f_empty_when_counter_0 : assert property (
        @(posedge clock)
        (fifo.counter == 4'd0) |-> f_empty
    );

    f_empty_only_when_counter_0 : assert property (
        @(posedge clock)
        f_empty |-> (fifo.counter == 4'd0)
    );

    // -------------------------------------------------------------------------
    // f_full and f_empty are mutually exclusive
    // -------------------------------------------------------------------------

    full_and_empty_mutually_exclusive : assert property (
        @(posedge clock)
        !(f_full && f_empty)
    );

    // -------------------------------------------------------------------------
    // Reset behaviour
    // -------------------------------------------------------------------------

    reset_wr_ptr_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.wr_ptr == {AWIDTH{1'b0}})
    );

    reset_rd_ptr_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.rd_ptr == {AWIDTH{1'b0}})
    );

    reset_counter_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.counter == {AWIDTH{1'b0}})
    );

    // -------------------------------------------------------------------------
    // Counter bounds
    // -------------------------------------------------------------------------

    counter_never_exceeds_max : assert property (
        @(posedge clock) disable iff (reset)
        fifo.counter <= 4'd15
    );

    // -------------------------------------------------------------------------
    // Write pointer increments on valid write
    // -------------------------------------------------------------------------

    wr_ptr_increments_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.wr_ptr == ($past(fifo.wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    wr_ptr_stable_when_no_write : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=>
        (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------------
    // Read pointer increments on valid read
    // -------------------------------------------------------------------------

    rd_ptr_increments_on_valid_read : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=>
        (fifo.rd_ptr == ($past(fifo.rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    rd_ptr_stable_when_no_read : assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=>
        (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------------
    // Counter increments on write-only
    // -------------------------------------------------------------------------

    counter_increments_on_write_only : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=>
        (fifo.counter == ($past(fifo.counter) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // -------------------------------------------------------------------------
    // Counter decrements on read-only
    // -------------------------------------------------------------------------

    counter_decrements_on_read_only : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=>
        (fifo.counter == ($past(fifo.counter) - {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // -------------------------------------------------------------------------
    // Counter stable when both wr and rd active simultaneously (or neither)
    // -------------------------------------------------------------------------

    counter_stable_on_simultaneous_rd_wr : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=>
        (fifo.counter == $past(fifo.counter))
    );

    counter_stable_when_no_valid_op : assert property (
        @(posedge clock) disable iff (reset)
        ((!wr_en || f_full) && (!rd_en || f_empty)) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // No write when full
    // -------------------------------------------------------------------------

    no_write_when_full : assert property (
        @(posedge clock) disable iff (reset)
        f_full |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------------
    // No read when empty
    // -------------------------------------------------------------------------

    no_read_when_empty : assert property (
        @(posedge clock) disable iff (reset)
        f_empty |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------------
    // data_out reflects mem[rd_ptr]
    // -------------------------------------------------------------------------

    data_out_reflects_mem_rd_ptr : assert property (
        @(posedge clock) disable iff (reset)
        data_out == fifo.mem[fifo.rd_ptr]
    );

    // -------------------------------------------------------------------------
    // Write stores data_in at wr_ptr
    // -------------------------------------------------------------------------

    write_stores_data_at_wr_ptr : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

    // -------------------------------------------------------------------------
    // Counter stays non-negative (already guaranteed by unsigned, but explicit)
    // -------------------------------------------------------------------------

    counter_non_negative : assert property (
        @(posedge clock) disable iff (reset)
        fifo.counter >= {AWIDTH{1'b0}}
    );

    // -------------------------------------------------------------------------
    // f_full asserted => wr_ptr would wrap if written (counter at max)
    // -------------------------------------------------------------------------

    full_implies_counter_max : assert property (
        @(posedge clock)
        f_full <-> (fifo.counter == 4'd15)
    );

    empty_implies_counter_min : assert property (
        @(posedge clock)
        f_empty <-> (fifo.counter == 4'd0)
    );

    // -------------------------------------------------------------------------
    // wr pointer assignment wire correctness
    // -------------------------------------------------------------------------

    wr_wire_correct_when_enabled : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |->
        (fifo.wr == fifo.wr_ptr + 4'd1)
    );

    wr_wire_correct_when_disabled : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |->
        (fifo.wr == fifo.wr_ptr)
    );

    // -------------------------------------------------------------------------
    // rd pointer assignment wire correctness
    // -------------------------------------------------------------------------

    rd_wire_correct_when_enabled : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |->
        (fifo.rd == fifo.rd_ptr + 4'd1)
    );

    rd_wire_correct_when_disabled : assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |->
        (fifo.rd == fifo.rd_ptr)
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
