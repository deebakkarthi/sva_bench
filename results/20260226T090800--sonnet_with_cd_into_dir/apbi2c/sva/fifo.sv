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

    // f_full is asserted when counter == 15
    full_when_counter_15: assert property (
        @(posedge clock) (fifo.counter == 4'd15) |-> f_full
    );

    // f_empty is asserted when counter == 0
    empty_when_counter_0: assert property (
        @(posedge clock) (fifo.counter == 4'd0) |-> f_empty
    );

    // f_full implies counter == 15
    full_implies_counter_15: assert property (
        @(posedge clock) f_full |-> (fifo.counter == 4'd15)
    );

    // f_empty implies counter == 0
    empty_implies_counter_0: assert property (
        @(posedge clock) f_empty |-> (fifo.counter == 4'd0)
    );

    // Cannot be full and empty at the same time (for DEPTH > 1)
    not_full_and_empty: assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // Write pointer increments on valid write
    wr_ptr_increments: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1))
    );

    // Write pointer stable when not writing or full
    wr_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer increments on valid read
    rd_ptr_increments: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1))
    );

    // Read pointer stable when not reading or empty
    rd_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter increments on write-only (no simultaneous read)
    counter_increments_on_write: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=> (fifo.counter == ($past(fifo.counter) + 4'd1))
    );

    // Counter decrements on read-only (no simultaneous write)
    counter_decrements_on_read: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=> (fifo.counter == ($past(fifo.counter) - 4'd1))
    );

    // Counter stable on simultaneous read and write (both valid)
    counter_stable_on_rw: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter stable when no valid operation
    counter_stable_no_op: assert property (
        @(posedge clock) disable iff (reset)
        ((!wr_en || f_full) && (!rd_en || f_empty)) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter never exceeds 15
    counter_no_overflow: assert property (
        @(posedge clock) (fifo.counter <= 4'd15)
    );

    // No write when full
    no_write_when_full: assert property (
        @(posedge clock) disable iff (reset)
        (f_full && wr_en && !rd_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // No read when empty
    no_read_when_empty: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && rd_en && !wr_en) |=> (fifo.counter == $past(fifo.counter))
    );

    // data_out reflects mem at rd_ptr
    data_out_correct: assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    // Write pointer stable on full
    wr_ptr_stable_on_full: assert property (
        @(posedge clock) disable iff (reset)
        (f_full) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer stable on empty
    rd_ptr_stable_on_empty: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
