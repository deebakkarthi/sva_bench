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

    // f_full is asserted when and only when counter == 15
    f_full_when_counter_max: assert property (
        @(posedge clock) (fifo.counter == 4'd15) |-> f_full
    );

    f_full_only_when_counter_max: assert property (
        @(posedge clock) f_full |-> (fifo.counter == 4'd15)
    );

    // f_empty is asserted when and only when counter == 0
    f_empty_when_counter_zero: assert property (
        @(posedge clock) (fifo.counter == 4'd0) |-> f_empty
    );

    f_empty_only_when_counter_zero: assert property (
        @(posedge clock) f_empty |-> (fifo.counter == 4'd0)
    );

    // f_full and f_empty are mutually exclusive
    full_and_empty_mutually_exclusive: assert property (
        @(posedge clock) f_full |-> !f_empty
    );

    empty_and_full_mutually_exclusive: assert property (
        @(posedge clock) f_empty |-> !f_full
    );

    // On reset, wr_ptr is cleared
    reset_wr_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    // On reset, rd_ptr is cleared
    reset_rd_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    // On reset, counter is cleared
    reset_counter_zero: assert property (
        @(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    // On reset, f_empty is asserted
    reset_fifo_empty: assert property (
        @(posedge clock) reset |=> f_empty
    );

    // On reset, f_full is deasserted
    reset_fifo_not_full: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // Write pointer increments on successful write (wr_en && !f_full)
    wr_ptr_increments_on_write: assert property (
        @(posedge clock) !reset && wr_en && !f_full |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // Write pointer holds when FIFO is full during write attempt
    wr_ptr_holds_when_full: assert property (
        @(posedge clock) !reset && wr_en && f_full |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Write pointer holds when wr_en is deasserted
    wr_ptr_holds_when_no_write: assert property (
        @(posedge clock) !reset && !wr_en |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer increments on successful read (rd_en && !f_empty)
    rd_ptr_increments_on_read: assert property (
        @(posedge clock) !reset && rd_en && !f_empty |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // Read pointer holds when FIFO is empty during read attempt
    rd_ptr_holds_when_empty: assert property (
        @(posedge clock) !reset && rd_en && f_empty |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Read pointer holds when rd_en is deasserted
    rd_ptr_holds_when_no_read: assert property (
        @(posedge clock) !reset && !rd_en |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter increments on write-only (wr_en && !f_full && !rd_en)
    counter_increments_on_write_only: assert property (
        @(posedge clock) !reset && wr_en && !f_full && !rd_en |=> (fifo.counter == ($past(fifo.counter) + {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // Counter decrements on read-only (rd_en && !f_empty && !wr_en)
    counter_decrements_on_read_only: assert property (
        @(posedge clock) !reset && rd_en && !f_empty && !wr_en |=> (fifo.counter == ($past(fifo.counter) - {{(AWIDTH-1){1'b0}}, 1'b1}))
    );

    // Counter unchanged on simultaneous read and write (both valid)
    counter_stable_on_simultaneous_rw: assert property (
        @(posedge clock) !reset && wr_en && !f_full && rd_en && !f_empty |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter unchanged when no valid read or write
    counter_stable_when_no_rw: assert property (
        @(posedge clock) !reset && (!wr_en || f_full) && (!rd_en || f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // Counter never exceeds depth minus 1 (15)
    counter_never_exceeds_max: assert property (
        @(posedge clock) !reset |-> (fifo.counter <= 4'd15)
    );

    // No write occurs when FIFO is full (wr_ptr does not change)
    no_write_when_full: assert property (
        @(posedge clock) !reset && f_full && wr_en && !rd_en |=> (fifo.wr_ptr == $past(fifo.wr_ptr)) && (fifo.counter == $past(fifo.counter))
    );

    // No read occurs when FIFO is empty (rd_ptr does not change)
    no_read_when_empty: assert property (
        @(posedge clock) !reset && f_empty && rd_en && !wr_en |=> (fifo.rd_ptr == $past(fifo.rd_ptr)) && (fifo.counter == $past(fifo.counter))
    );

    // data_out reflects the memory at current rd_ptr
    data_out_reflects_rd_ptr: assert property (
        @(posedge clock) 1'b1 |-> (data_out == fifo.mem[fifo.rd_ptr])
    );

    // After a successful write, memory at wr_ptr contains data_in
    write_stores_data_in_mem: assert property (
        @(posedge clock) !reset && wr_en && !f_full |=> (fifo.mem[$past(fifo.wr_ptr)] == $past(data_in))
    );

    // f_empty asserted after reset then stays empty without write
    empty_persists_without_write: assert property (
        @(posedge clock) !reset && f_empty && !wr_en |=> f_empty
    );

    // f_full persists without a read
    full_persists_without_read: assert property (
        @(posedge clock) !reset && f_full && !rd_en |=> f_full
    );

    // After one write into empty FIFO, FIFO is no longer empty
    write_clears_empty: assert property (
        @(posedge clock) !reset && f_empty && wr_en |=> !f_empty
    );

    // After one read from one-entry FIFO, FIFO becomes empty
    read_last_entry_makes_empty: assert property (
        @(posedge clock) !reset && (fifo.counter == 4'd1) && rd_en && !wr_en |=> f_empty
    );

    // Writing to full FIFO with no read does not change full status
    write_to_full_stays_full: assert property (
        @(posedge clock) !reset && f_full && wr_en && !rd_en |=> f_full
    );

    // Reading from full FIFO clears full status
    read_from_full_clears_full: assert property (
        @(posedge clock) !reset && f_full && rd_en && !wr_en |=> !f_full
    );

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
