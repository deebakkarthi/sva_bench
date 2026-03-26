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

    // ------------------------------------------------------------------
    // Combinational output correctness
    // ------------------------------------------------------------------

    f_full_iff_counter_equals_fifteen : assert property (
        @(posedge clock) f_full == (fifo.counter == 4'd15)
    );

    f_empty_iff_counter_equals_zero : assert property (
        @(posedge clock) f_empty == (fifo.counter == 4'd0)
    );

    full_and_empty_mutually_exclusive : assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    data_out_equals_mem_at_rd_ptr : assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    // ------------------------------------------------------------------
    // wr / rd wire correctness
    // ------------------------------------------------------------------

    wr_wire_increments_on_valid_write : assert property (
        @(posedge clock) (wr_en && !f_full) |-> (fifo.wr == (fifo.wr_ptr + 4'd1))
    );

    wr_wire_holds_on_invalid_write : assert property (
        @(posedge clock) !(wr_en && !f_full) |-> (fifo.wr == fifo.wr_ptr)
    );

    rd_wire_increments_on_valid_read : assert property (
        @(posedge clock) (rd_en && !f_empty) |-> (fifo.rd == (fifo.rd_ptr + 4'd1))
    );

    rd_wire_holds_on_invalid_read : assert property (
        @(posedge clock) !(rd_en && !f_empty) |-> (fifo.rd == fifo.rd_ptr)
    );

    // ------------------------------------------------------------------
    // w_counter wire correctness
    // ------------------------------------------------------------------

    w_counter_decrements_on_read_only : assert property (
        @(posedge clock) (rd_en && !f_empty && !wr_en) |->
        (fifo.w_counter == (fifo.counter - 4'd1))
    );

    w_counter_increments_on_write_only : assert property (
        @(posedge clock) (wr_en && !f_full && !rd_en) |->
        (fifo.w_counter == (fifo.counter + 4'd1))
    );

    // ------------------------------------------------------------------
    // Reset behaviour (reset is active HIGH)
    // ------------------------------------------------------------------

    wr_ptr_resets_to_zero : assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {AWIDTH{1'b0}})
    );

    rd_ptr_resets_to_zero : assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {AWIDTH{1'b0}})
    );

    counter_resets_to_zero : assert property (
        @(posedge clock) reset |=> (fifo.counter == {AWIDTH{1'b0}})
    );

    f_empty_asserted_after_reset : assert property (
        @(posedge clock) reset |=> f_empty
    );

    f_full_deasserted_after_reset : assert property (
        @(posedge clock) reset |=> !f_full
    );

    // ------------------------------------------------------------------
    // Write pointer behaviour
    // ------------------------------------------------------------------

    wr_ptr_increments_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1))
    );

    wr_ptr_stable_when_full : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    wr_ptr_stable_when_wr_en_deasserted : assert property (
        @(posedge clock) disable iff (reset)
        !wr_en |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // ------------------------------------------------------------------
    // Read pointer behaviour
    // ------------------------------------------------------------------

    rd_ptr_increments_on_valid_read : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1))
    );

    rd_ptr_stable_when_empty : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    rd_ptr_stable_when_rd_en_deasserted : assert property (
        @(posedge clock) disable iff (reset)
        !rd_en |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // ------------------------------------------------------------------
    // Counter behaviour
    // ------------------------------------------------------------------

    counter_bounded_between_zero_and_fifteen : assert property (
        @(posedge clock) fifo.counter <= 4'd15
    );

    counter_increments_on_write_only : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=> (fifo.counter == ($past(fifo.counter) + 4'd1))
    );

    counter_decrements_on_read_only : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=> (fifo.counter == ($past(fifo.counter) - 4'd1))
    );

    counter_stable_on_simultaneous_valid_read_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    counter_stable_when_no_operation : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    counter_stable_on_write_to_full_fifo : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    counter_stable_on_read_from_empty_fifo : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter))
    );

    counter_at_max_when_full : assert property (
        @(posedge clock) f_full |-> (fifo.counter == 4'd15)
    );

    counter_at_zero_when_empty : assert property (
        @(posedge clock) f_empty |-> (fifo.counter == 4'd0)
    );

    counter_cannot_exceed_max : assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd15) |=> (fifo.counter <= 4'd15)
    );

    counter_cannot_go_below_zero : assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd0) |=> (fifo.counter >= 4'd0)
    );

    // ------------------------------------------------------------------
    // Memory write correctness
    // ------------------------------------------------------------------

    mem_written_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

    // ------------------------------------------------------------------
    // No write when FIFO is full
    // ------------------------------------------------------------------

    no_wr_ptr_advance_when_full : assert property (
        @(posedge clock) disable iff (reset)
        f_full |-> (fifo.wr == fifo.wr_ptr)
    );

    // ------------------------------------------------------------------
    // No read pointer advance when FIFO is empty
    // ------------------------------------------------------------------

    no_rd_ptr_advance_when_empty : assert property (
        @(posedge clock) disable iff (reset)
        f_empty |-> (fifo.rd == fifo.rd_ptr)
    );

    // ------------------------------------------------------------------
    // f_full deasserted after a valid read
    // ------------------------------------------------------------------

    full_deasserted_after_read : assert property (
        @(posedge clock) disable iff (reset)
        (f_full && rd_en && !wr_en) |=> !f_full
    );

    // ------------------------------------------------------------------
    // f_empty deasserted after a valid write
    // ------------------------------------------------------------------

    empty_deasserted_after_write : assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && wr_en && !rd_en) |=> !f_empty
    );

    // ------------------------------------------------------------------
    // Pointer and counter widths stay within AWIDTH bits
    // ------------------------------------------------------------------

    wr_ptr_within_awidth : assert property (
        @(posedge clock) fifo.wr_ptr <= {AWIDTH{1'b1}}
    );

    rd_ptr_within_awidth : assert property (
        @(posedge clock) fifo.rd_ptr <= {AWIDTH{1'b1}}
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
