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

    // -------------------------------------------------------------------------
    // f_full and f_empty combinational correctness
    // -------------------------------------------------------------------------

    f_full_when_counter_equals_15 : assert property (
        @(posedge clock)
        f_full === (fifo.counter == 4'd15)
    );

    f_empty_when_counter_equals_zero : assert property (
        @(posedge clock)
        f_empty === (fifo.counter == 4'd0)
    );

    f_full_and_f_empty_mutually_exclusive : assert property (
        @(posedge clock)
        !(f_full && f_empty)
    );

    // -------------------------------------------------------------------------
    // Reset behavior (active high reset)
    // -------------------------------------------------------------------------

    reset_wr_ptr_to_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.wr_ptr === {(AWIDTH){1'b0}})
    );

    reset_rd_ptr_to_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.rd_ptr === {(AWIDTH){1'b0}})
    );

    reset_counter_to_zero : assert property (
        @(posedge clock)
        reset |=> (fifo.counter === {(AWIDTH){1'b0}})
    );

    // -------------------------------------------------------------------------
    // Counter bounds
    // -------------------------------------------------------------------------

    counter_never_exceeds_depth_minus_one : assert property (
        @(posedge clock)
        fifo.counter <= 4'd15
    );

    wr_ptr_within_valid_range : assert property (
        @(posedge clock)
        fifo.wr_ptr <= 4'd15
    );

    rd_ptr_within_valid_range : assert property (
        @(posedge clock)
        fifo.rd_ptr <= 4'd15
    );

    // -------------------------------------------------------------------------
    // Write pointer behavior
    // -------------------------------------------------------------------------

    wr_ptr_increments_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.wr_ptr === ($past(fifo.wr_ptr) + 4'd1))
    );

    wr_ptr_stable_when_full : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full) |=>
        (fifo.wr_ptr === $past(fifo.wr_ptr))
    );

    wr_ptr_stable_when_wr_en_deasserted : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en) |=>
        (fifo.wr_ptr === $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------------
    // Read pointer behavior
    // -------------------------------------------------------------------------

    rd_ptr_increments_on_valid_read : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=>
        (fifo.rd_ptr === ($past(fifo.rd_ptr) + 4'd1))
    );

    rd_ptr_stable_when_empty : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty) |=>
        (fifo.rd_ptr === $past(fifo.rd_ptr))
    );

    rd_ptr_stable_when_rd_en_deasserted : assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en) |=>
        (fifo.rd_ptr === $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------------
    // Counter behavior
    // -------------------------------------------------------------------------

    counter_increments_on_write_only : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=>
        (fifo.counter === ($past(fifo.counter) + 4'd1))
    );

    counter_decrements_on_read_only : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=>
        (fifo.counter === ($past(fifo.counter) - 4'd1))
    );

    counter_stable_on_simultaneous_read_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=>
        (fifo.counter === $past(fifo.counter))
    );

    counter_stable_when_no_valid_transaction : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=>
        (fifo.counter === $past(fifo.counter))
    );

    counter_stable_when_write_to_full : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full && !rd_en) |=>
        (fifo.counter === $past(fifo.counter))
    );

    counter_stable_when_read_from_empty : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty && !wr_en) |=>
        (fifo.counter === $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // No overflow: counter must not wrap when full
    // -------------------------------------------------------------------------

    counter_does_not_overflow_when_full : assert property (
        @(posedge clock) disable iff (reset)
        f_full |=> (fifo.counter <= 4'd15)
    );

    // -------------------------------------------------------------------------
    // No underflow: counter must not wrap when empty
    // -------------------------------------------------------------------------

    counter_does_not_underflow_when_empty : assert property (
        @(posedge clock) disable iff (reset)
        f_empty |=> (fifo.counter <= 4'd15)
    );

    // -------------------------------------------------------------------------
    // f_full asserted after counter reaches 15
    // -------------------------------------------------------------------------

    f_full_asserted_when_counter_reaches_max : assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd15) |-> f_full
    );

    f_empty_asserted_when_counter_is_zero : assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd0) |-> f_empty
    );

    // -------------------------------------------------------------------------
    // f_full deasserts after a valid read
    // -------------------------------------------------------------------------

    f_full_deasserts_after_valid_read : assert property (
        @(posedge clock) disable iff (reset)
        (f_full && rd_en) |=> !f_full
    );

    // -------------------------------------------------------------------------
    // f_empty deasserts after a valid write
    // -------------------------------------------------------------------------

    f_empty_deasserts_after_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && wr_en) |=> !f_empty
    );

    // -------------------------------------------------------------------------
    // Write pointer advances to next slot combinationally
    // -------------------------------------------------------------------------

    wr_wire_equals_wr_ptr_plus_one_on_write : assert property (
        @(posedge clock)
        (wr_en && !f_full) |-> (fifo.wr === fifo.wr_ptr + 4'd1)
    );

    wr_wire_equals_wr_ptr_when_not_writing : assert property (
        @(posedge clock)
        (!wr_en || f_full) |-> (fifo.wr === fifo.wr_ptr)
    );

    // -------------------------------------------------------------------------
    // Read pointer advances to next slot combinationally
    // -------------------------------------------------------------------------

    rd_wire_equals_rd_ptr_plus_one_on_read : assert property (
        @(posedge clock)
        (rd_en && !f_empty) |-> (fifo.rd === fifo.rd_ptr + 4'd1)
    );

    rd_wire_equals_rd_ptr_when_not_reading : assert property (
        @(posedge clock)
        (!rd_en || f_empty) |-> (fifo.rd === fifo.rd_ptr)
    );

    // -------------------------------------------------------------------------
    // data_out reflects memory at read pointer
    // -------------------------------------------------------------------------

    data_out_reflects_mem_at_rd_ptr : assert property (
        @(posedge clock)
        data_out === fifo.mem[fifo.rd_ptr]
    );

    // -------------------------------------------------------------------------
    // Memory write: data stored at write pointer on valid write
    // -------------------------------------------------------------------------

    mem_written_with_data_in_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.mem[$past(fifo.wr_ptr)] === $past(data_in))
    );

    // -------------------------------------------------------------------------
    // f_full only asserts once counter reaches maximum
    // -------------------------------------------------------------------------

    f_full_only_when_counter_at_max : assert property (
        @(posedge clock)
        f_full |-> (fifo.counter == 4'd15)
    );

    f_empty_only_when_counter_at_zero : assert property (
        @(posedge clock)
        f_empty |-> (fifo.counter == 4'd0)
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
