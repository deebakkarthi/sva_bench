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

    // Internal signal access via hierarchical references
    wire [AWIDTH-1:0] wr_ptr   = fifo_assert_instance.wr_ptr;
    wire [AWIDTH-1:0] rd_ptr   = fifo_assert_instance.rd_ptr;
    wire [AWIDTH-1:0] counter  = fifo_assert_instance.counter;

    // --- Reset assertions ---
    reset_clears_wr_ptr : assert property (
        @(posedge clock) reset |=> (wr_ptr == {AWIDTH{1'b0}})
    );

    reset_clears_rd_ptr : assert property (
        @(posedge clock) reset |=> (rd_ptr == {AWIDTH{1'b0}})
    );

    reset_clears_counter : assert property (
        @(posedge clock) reset |=> (counter == {AWIDTH{1'b0}})
    );

    // --- Full/Empty flag correctness ---
    f_full_when_counter_max : assert property (
        @(posedge clock) (counter == 4'd15) |-> f_full
    );

    f_full_only_when_counter_max : assert property (
        @(posedge clock) f_full |-> (counter == 4'd15)
    );

    f_empty_when_counter_zero : assert property (
        @(posedge clock) (counter == 4'd0) |-> f_empty
    );

    f_empty_only_when_counter_zero : assert property (
        @(posedge clock) f_empty |-> (counter == 4'd0)
    );

    full_and_empty_mutually_exclusive : assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // --- Counter bounds ---
    counter_never_exceeds_max : assert property (
        @(posedge clock) !reset |-> (counter <= 4'd15)
    );

    counter_never_below_zero : assert property (
        @(posedge clock) !reset |-> (counter >= 4'd0)
    );

    // --- Write pointer behavior ---
    wr_ptr_increments_on_valid_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=> (wr_ptr == ($past(wr_ptr) + 4'd1))
    );

    wr_ptr_stable_when_no_write : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=> (wr_ptr == $past(wr_ptr))
    );

    // --- Read pointer behavior ---
    rd_ptr_increments_on_valid_read : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=> (rd_ptr == ($past(rd_ptr) + 4'd1))
    );

    rd_ptr_stable_when_no_read : assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=> (rd_ptr == $past(rd_ptr))
    );

    // --- Counter update behavior ---
    counter_increments_on_write_only : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=> (counter == ($past(counter) + 4'd1))
    );

    counter_decrements_on_read_only : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=> (counter == ($past(counter) - 4'd1))
    );

    counter_stable_on_concurrent_read_write : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=> (counter == $past(counter))
    );

    counter_stable_on_no_operation : assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=> (counter == $past(counter))
    );

    counter_stable_when_write_full : assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full && !rd_en) |=> (counter == $past(counter))
    );

    counter_stable_when_read_empty : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty && !wr_en) |=> (counter == $past(counter))
    );

    // --- No write when full ---
    no_write_when_full : assert property (
        @(posedge clock) disable iff (reset)
        f_full |-> !wr_en || (wr_en && counter == $past(counter))
    );

    // --- After reset, FIFO is empty ---
    fifo_empty_after_reset : assert property (
        @(posedge clock) $rose(!reset) |-> f_empty
    );

    // --- data_out stability: rd_ptr only changes on valid read ---
    rd_ptr_no_change_on_empty_read : assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty) |=> (rd_ptr == $past(rd_ptr))
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
