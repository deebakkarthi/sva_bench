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
    // f_full asserted only when counter == 15
    // -------------------------------------------------------------------------
    full_when_counter_15: assert property (
        @(posedge clock) f_full == (fifo.counter == 4'd15)
    );

    // -------------------------------------------------------------------------
    // f_empty asserted only when counter == 0
    // -------------------------------------------------------------------------
    empty_when_counter_0: assert property (
        @(posedge clock) f_empty == (fifo.counter == 4'd0)
    );

    // -------------------------------------------------------------------------
    // FIFO cannot be both full and empty simultaneously
    // -------------------------------------------------------------------------
    not_full_and_empty: assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // -------------------------------------------------------------------------
    // On reset: wr_ptr is 0
    // -------------------------------------------------------------------------
    reset_wr_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    // -------------------------------------------------------------------------
    // On reset: rd_ptr is 0
    // -------------------------------------------------------------------------
    reset_rd_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    // -------------------------------------------------------------------------
    // On reset: counter is 0
    // -------------------------------------------------------------------------
    reset_counter_zero: assert property (
        @(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    // -------------------------------------------------------------------------
    // On reset: f_empty is asserted next cycle
    // -------------------------------------------------------------------------
    reset_causes_empty: assert property (
        @(posedge clock) reset |=> f_empty
    );

    // -------------------------------------------------------------------------
    // On reset: f_full is deasserted next cycle
    // -------------------------------------------------------------------------
    reset_clears_full: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // -------------------------------------------------------------------------
    // Write-only increments counter by 1
    // -------------------------------------------------------------------------
    write_only_increments_counter: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en) |=>
        (fifo.counter == $past(fifo.counter) + 4'd1)
    );

    // -------------------------------------------------------------------------
    // Read-only decrements counter by 1
    // -------------------------------------------------------------------------
    read_only_decrements_counter: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en) |=>
        (fifo.counter == $past(fifo.counter) - 4'd1)
    );

    // -------------------------------------------------------------------------
    // Simultaneous read and write: counter unchanged
    // -------------------------------------------------------------------------
    simultaneous_rw_counter_stable: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && rd_en && !f_empty) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // No write when full: wr_ptr unchanged
    // -------------------------------------------------------------------------
    no_write_when_full_wr_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full) |=>
        (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------------
    // No read when empty: rd_ptr unchanged
    // -------------------------------------------------------------------------
    no_read_when_empty_rd_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty) |=>
        (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------------
    // No write when full: counter unchanged
    // -------------------------------------------------------------------------
    no_write_when_full_counter_stable: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full && !rd_en) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // No read when empty: counter unchanged
    // -------------------------------------------------------------------------
    no_read_when_empty_counter_stable: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && f_empty && !wr_en) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // Write-only: wr_ptr increments by 1
    // -------------------------------------------------------------------------
    write_increments_wr_ptr: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.wr_ptr == $past(fifo.wr_ptr) + 4'd1)
    );

    // -------------------------------------------------------------------------
    // Read-only: rd_ptr increments by 1
    // -------------------------------------------------------------------------
    read_increments_rd_ptr: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |=>
        (fifo.rd_ptr == $past(fifo.rd_ptr) + 4'd1)
    );

    // -------------------------------------------------------------------------
    // No activity: wr_ptr stable
    // -------------------------------------------------------------------------
    no_write_wr_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |=>
        (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // -------------------------------------------------------------------------
    // No activity: rd_ptr stable
    // -------------------------------------------------------------------------
    no_read_rd_ptr_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |=>
        (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // -------------------------------------------------------------------------
    // counter is always bounded within [0, 15]
    // -------------------------------------------------------------------------
    counter_upper_bound: assert property (
        @(posedge clock) fifo.counter <= 4'd15
    );

    // -------------------------------------------------------------------------
    // f_full implies counter is at maximum
    // -------------------------------------------------------------------------
    full_implies_max_counter: assert property (
        @(posedge clock) f_full |-> (fifo.counter == 4'd15)
    );

    // -------------------------------------------------------------------------
    // f_empty implies counter is zero
    // -------------------------------------------------------------------------
    empty_implies_zero_counter: assert property (
        @(posedge clock) f_empty |-> (fifo.counter == 4'd0)
    );

    // -------------------------------------------------------------------------
    // When not full and not writing, f_full remains deasserted
    // -------------------------------------------------------------------------
    full_not_asserted_without_write: assert property (
        @(posedge clock) disable iff (reset)
        (!f_full && !wr_en) |=> !f_full
    );

    // -------------------------------------------------------------------------
    // When not empty and not reading, f_empty stays deasserted
    // -------------------------------------------------------------------------
    empty_not_asserted_without_read: assert property (
        @(posedge clock) disable iff (reset)
        (!f_empty && !wr_en && !rd_en) |=> !f_empty
    );

    // -------------------------------------------------------------------------
    // data_out always reflects mem[rd_ptr]
    // -------------------------------------------------------------------------
    data_out_reflects_mem_rd_ptr: assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    // -------------------------------------------------------------------------
    // After write, mem at previous wr_ptr holds written data
    // -------------------------------------------------------------------------
    write_stores_data_in_mem: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |=>
        (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

    // -------------------------------------------------------------------------
    // After write-only, becoming full requires counter was at 14
    // -------------------------------------------------------------------------
    write_causes_full_only_at_14: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full && !rd_en && fifo.counter == 4'd14) |=> f_full
    );

    // -------------------------------------------------------------------------
    // After read-only, becoming empty requires counter was at 1
    // -------------------------------------------------------------------------
    read_causes_empty_only_at_1: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty && !wr_en && fifo.counter == 4'd1) |=> f_empty
    );

    // -------------------------------------------------------------------------
    // When neither read nor write: counter remains stable
    // -------------------------------------------------------------------------
    no_rw_counter_stable: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en && !rd_en) |=>
        (fifo.counter == $past(fifo.counter))
    );

    // -------------------------------------------------------------------------
    // wr wire: equals wr_ptr+1 when wr_en and not full, else wr_ptr
    // -------------------------------------------------------------------------
    wr_wire_correct_when_wr_en: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && !f_full) |->
        (fifo.wr == fifo.wr_ptr + 4'd1)
    );

    wr_wire_correct_when_no_write: assert property (
        @(posedge clock) disable iff (reset)
        (!wr_en || f_full) |->
        (fifo.wr == fifo.wr_ptr)
    );

    // -------------------------------------------------------------------------
    // rd wire: equals rd_ptr+1 when rd_en and not empty, else rd_ptr
    // -------------------------------------------------------------------------
    rd_wire_correct_when_rd_en: assert property (
        @(posedge clock) disable iff (reset)
        (rd_en && !f_empty) |->
        (fifo.rd == fifo.rd_ptr + 4'd1)
    );

    rd_wire_correct_when_no_read: assert property (
        @(posedge clock) disable iff (reset)
        (!rd_en || f_empty) |->
        (fifo.rd == fifo.rd_ptr)
    );

    // -------------------------------------------------------------------------
    // Write when full: data not written (mem unchanged at wr_ptr)
    // -------------------------------------------------------------------------
    no_write_to_mem_when_full: assert property (
        @(posedge clock) disable iff (reset)
        (wr_en && f_full) |=>
        (fifo.mem[$past(fifo.wr_ptr)] == $past(fifo.mem[$past(fifo.wr_ptr)]))
    );

    // -------------------------------------------------------------------------
    // Counter never overflows when full
    // -------------------------------------------------------------------------
    counter_no_overflow_when_full: assert property (
        @(posedge clock) disable iff (reset)
        (f_full && !rd_en) |=> (fifo.counter == 4'd15)
    );

    // -------------------------------------------------------------------------
    // Counter never underflows when empty
    // -------------------------------------------------------------------------
    counter_no_underflow_when_empty: assert property (
        @(posedge clock) disable iff (reset)
        (f_empty && !wr_en) |=> (fifo.counter == 4'd0)
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
