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

    // -------------------------------------------------------------------
    // f_full and f_empty correctness
    // -------------------------------------------------------------------

    f_full_when_counter_15: assert property (
        @(posedge clock)
        (fifo.counter == 4'd15) |-> (f_full == 1'b1)
    );

    f_not_full_when_counter_not_15: assert property (
        @(posedge clock)
        (fifo.counter != 4'd15) |-> (f_full == 1'b0)
    );

    f_empty_when_counter_0: assert property (
        @(posedge clock)
        (fifo.counter == 4'd0) |-> (f_empty == 1'b1)
    );

    f_not_empty_when_counter_not_0: assert property (
        @(posedge clock)
        (fifo.counter != 4'd0) |-> (f_empty == 1'b0)
    );

    // -------------------------------------------------------------------
    // Cannot be full and empty simultaneously
    // -------------------------------------------------------------------

    not_full_and_empty: assert property (
        @(posedge clock)
        !(f_full && f_empty)
    );

    // -------------------------------------------------------------------
    // Reset behavior
    // -------------------------------------------------------------------

    wr_ptr_reset_to_zero: assert property (
        @(posedge clock)
        $rose(reset) |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    rd_ptr_reset_to_zero: assert property (
        @(posedge clock)
        $rose(reset) |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    counter_reset_to_zero: assert property (
        @(posedge clock)
        $rose(reset) |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    f_empty_after_reset: assert property (
        @(posedge clock)
        $rose(reset) |=> (f_empty == 1'b1)
    );

    f_not_full_after_reset: assert property (
        @(posedge clock)
        $rose(reset) |=> (f_full == 1'b0)
    );

    // -------------------------------------------------------------------
    // Write pointer increments on valid write
    // -------------------------------------------------------------------

    wr_ptr_increments_on_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.wr_ptr == ($past(fifo.wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    wr_ptr_stable_when_no_write: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=>
        (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------
    // Read pointer increments on valid read
    // -------------------------------------------------------------------

    rd_ptr_increments_on_read: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=>
        (fifo.rd_ptr == ($past(fifo.rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    rd_ptr_stable_when_no_read: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=>
        (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------
    // Counter increments on write-only (no simultaneous read)
    // -------------------------------------------------------------------

    counter_increments_on_write_only: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=>
        (fifo.counter == ($past(fifo.counter) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // -------------------------------------------------------------------
    // Counter decrements on read-only (no simultaneous write)
    // -------------------------------------------------------------------

    counter_decrements_on_read_only: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=>
        (fifo.counter == ($past(fifo.counter) - {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // -------------------------------------------------------------------
    // Counter stable on simultaneous read and write (both valid)
    // -------------------------------------------------------------------

    counter_stable_on_simultaneous_rw: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------
    // Counter stable when no valid read or write
    // -------------------------------------------------------------------

    counter_stable_when_no_valid_op: assert property (
        @(posedge clock) disable iff (reset)
        ((!wr_en || f_full) && (!rd_en || f_empty)) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------
    // Counter bounded within valid range (0 to 15)
    // -------------------------------------------------------------------

    counter_bounded: assert property (
        @(posedge clock)
        fifo.counter <= 4'd15
    );

    // -------------------------------------------------------------------
    // No write when full
    // -------------------------------------------------------------------

    no_write_when_full: assert property (
        @(posedge clock) disable iff (reset)
        f_full |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------
    // No read when empty
    // -------------------------------------------------------------------

    no_read_when_empty: assert property (
        @(posedge clock) disable iff (reset)
        f_empty |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------
    // data_out always reflects mem[rd_ptr]
    // -------------------------------------------------------------------

    data_out_reflects_mem_rd_ptr: assert property (
        @(posedge clock)
        data_out == fifo.mem[fifo.rd_ptr]
    );

    // -------------------------------------------------------------------
    // Write data is stored at wr_ptr location
    // -------------------------------------------------------------------

    write_data_stored_correctly: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

    // -------------------------------------------------------------------
    // Counter never underflows (stays 0 when empty and read attempted)
    // -------------------------------------------------------------------

    counter_no_underflow: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && rd_en) |=>
        (fifo.counter == 4'd0)
    );

    // -------------------------------------------------------------------
    // Counter never overflows (stays at 15 when full and write attempted)
    // -------------------------------------------------------------------

    counter_no_overflow: assert property (
        @(posedge clock) disable iff (reset)
        (f_full && wr_en) |=>
        (fifo.counter == 4'd15)
    );

    // -------------------------------------------------------------------
    // wr_ptr does not change when full
    // -------------------------------------------------------------------

    wr_ptr_stable_when_full: assert property (
        @(posedge clock) disable iff (reset)
        f_full |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------
    // rd_ptr does not change when empty
    // -------------------------------------------------------------------

    rd_ptr_stable_when_empty: assert property (
        @(posedge clock) disable iff (reset)
        f_empty |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------
    // After reset deasserted and one write, FIFO is no longer empty
    // -------------------------------------------------------------------

    fifo_not_empty_after_write: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && wr_en && !f_full) |=> (!f_empty)
    );

    // -------------------------------------------------------------------
    // After counter reaches 1 and a read-only occurs, FIFO becomes empty
    // -------------------------------------------------------------------

    fifo_becomes_empty_after_last_read: assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd1 && rd_en && !wr_en) |=> (f_empty)
    );

    // -------------------------------------------------------------------
    // After counter reaches 14 and a write-only occurs, FIFO becomes full
    // -------------------------------------------------------------------

    fifo_becomes_full_after_last_write: assert property (
        @(posedge clock) disable iff (reset)
        (fifo.counter == 4'd14 && wr_en && !rd_en && !f_full) |=> (f_full)
    );

    // -------------------------------------------------------------------
    // wr_ptr and rd_ptr are always within valid address range
    // -------------------------------------------------------------------

    wr_ptr_in_valid_range: assert property (
        @(posedge clock)
        fifo.wr_ptr <= {(AWIDTH){1'b1}}
    );

    rd_ptr_in_valid_range: assert property (
        @(posedge clock)
        fifo.rd_ptr <= {(AWIDTH){1'b1}}
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
