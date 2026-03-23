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

    // f_full asserted iff counter == 15
    f_full_when_counter_max: assert property (
        @(posedge clock) (fifo.counter == 4'd15) |-> f_full
    );

    not_f_full_when_counter_not_max: assert property (
        @(posedge clock) (fifo.counter != 4'd15) |-> !f_full
    );

    f_full_implies_counter_max: assert property (
        @(posedge clock) f_full |-> (fifo.counter == 4'd15)
    );

    // f_empty asserted iff counter == 0
    f_empty_when_counter_zero: assert property (
        @(posedge clock) (fifo.counter == 4'd0) |-> f_empty
    );

    not_f_empty_when_counter_nonzero: assert property (
        @(posedge clock) (fifo.counter != 4'd0) |-> !f_empty
    );

    f_empty_implies_counter_zero: assert property (
        @(posedge clock) f_empty |-> (fifo.counter == 4'd0)
    );

    // f_full and f_empty are mutually exclusive
    full_implies_not_empty: assert property (
        @(posedge clock) f_full |-> !f_empty
    );

    empty_implies_not_full: assert property (
        @(posedge clock) f_empty |-> !f_full
    );

    // Combinational next write pointer
    wr_ptr_increments_when_wr_en_not_full: assert property (
        @(posedge clock) (wr_en && !f_full) |-> (fifo.wr == fifo.wr_ptr + 4'd1)
    );

    wr_ptr_holds_when_not_writing: assert property (
        @(posedge clock) !(wr_en && !f_full) |-> (fifo.wr == fifo.wr_ptr)
    );

    // Combinational next read pointer
    rd_ptr_increments_when_rd_en_not_empty: assert property (
        @(posedge clock) (rd_en && !f_empty) |-> (fifo.rd == fifo.rd_ptr + 4'd1)
    );

    rd_ptr_holds_when_not_reading: assert property (
        @(posedge clock) !(rd_en && !f_empty) |-> (fifo.rd == fifo.rd_ptr)
    );

    // Combinational w_counter: read only decrements counter
    w_counter_decrements_on_read_only: assert property (
        @(posedge clock) (rd_en && !f_empty && !wr_en) |-> (fifo.w_counter == fifo.counter - 4'd1)
    );

    // Combinational w_counter: write only increments counter
    w_counter_increments_on_write_only: assert property (
        @(posedge clock) (wr_en && !f_full && !rd_en) |-> (fifo.w_counter == fifo.counter + 4'd1)
    );

    // data_out always reflects mem at rd_ptr
    data_out_reflects_mem_at_rd_ptr: assert property (
        @(posedge clock) 1'b1 |-> (data_out == fifo.mem[fifo.rd_ptr])
    );

    // No write occurs when FIFO is full
    no_wr_ptr_advance_when_full: assert property (
        @(posedge clock) f_full |-> (fifo.wr == fifo.wr_ptr)
    );

    // No read occurs when FIFO is empty
    no_rd_ptr_advance_when_empty: assert property (
        @(posedge clock) f_empty |-> (fifo.rd == fifo.rd_ptr)
    );

    // Synchronous reset: write pointer cleared next cycle
    reset_clears_wr_ptr: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {AWIDTH{1'b0}})
    );

    // Synchronous reset: read pointer cleared next cycle
    reset_clears_rd_ptr: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {AWIDTH{1'b0}})
    );

    // Synchronous reset: counter cleared next cycle
    reset_clears_counter: assert property (
        @(posedge clock) reset |=> (fifo.counter == {AWIDTH{1'b0}})
    );

    // Synchronous reset: f_empty asserted two cycles after reset (counter goes to 0)
    reset_makes_fifo_empty: assert property (
        @(posedge clock) reset |=> f_empty
    );

    // Synchronous reset: f_full deasserted after reset
    reset_clears_full: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // Write pointer advances by 1 on valid write (next cycle)
    wr_ptr_advances_on_valid_write: assert property (
        @(posedge clock) (!reset && wr_en && !f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr) + 4'd1)
    );

    // Write pointer stable when no valid write (next cycle)
    wr_ptr_stable_when_no_write: assert property (
        @(posedge clock) (!reset && !(wr_en && !f_full)) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer advances by 1 on valid read (next cycle)
    rd_ptr_advances_on_valid_read: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr) + 4'd1)
    );

    // Read pointer stable when no valid read (next cycle)
    rd_ptr_stable_when_no_read: assert property (
        @(posedge clock) (!reset && !(rd_en && !f_empty)) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter decrements on read-only (next cycle)
    counter_decrements_on_read_only: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty && !wr_en) |=> (fifo.counter == $past(fifo.counter) - 4'd1)
    );

    // Counter increments on write-only (next cycle)
    counter_increments_on_write_only: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && !rd_en) |=> (fifo.counter == $past(fifo.counter) + 4'd1)
    );

    // Counter stable on simultaneous read and write (both valid, next cycle)
    counter_stable_on_simultaneous_read_write: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stable when no valid read and no valid write (next cycle)
    counter_stable_when_no_valid_op: assert property (
        @(posedge clock) (!reset && !(wr_en && !f_full) && !(rd_en && !f_empty)) |=> (fifo.counter == $past(fifo.counter))
    );

    // Write to full FIFO does not change write pointer (next cycle)
    wr_ptr_unchanged_when_full: assert property (
        @(posedge clock) (!reset && wr_en && f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read from empty FIFO does not change read pointer (next cycle)
    rd_ptr_unchanged_when_empty: assert property (
        @(posedge clock) (!reset && rd_en && f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter never exceeds 15
    counter_never_exceeds_max: assert property (
        @(posedge clock) 1'b1 |-> (fifo.counter <= 4'd15)
    );

    // f_full implies no counter increment possible
    full_no_increment: assert property (
        @(posedge clock) (!reset && f_full && !rd_en) |=> (fifo.counter == 4'd15)
    );

    // f_empty implies no counter decrement possible
    empty_no_decrement: assert property (
        @(posedge clock) (!reset && f_empty && !wr_en) |=> (fifo.counter == 4'd0)
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
