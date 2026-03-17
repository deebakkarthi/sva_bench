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

    // After reset, f_empty must be asserted
    reset_empty: assert property (
        @(posedge clock) reset |=> f_empty
    );

    // After reset, f_full must be deasserted
    reset_not_full: assert property (
        @(posedge clock) reset |=> !f_full
    );

    // f_full is set when counter == 15
    full_when_counter_15: assert property (
        @(posedge clock) (fifo.counter == 4'd15) |-> f_full
    );

    // f_empty is set when counter == 0
    empty_when_counter_0: assert property (
        @(posedge clock) (fifo.counter == 4'd0) |-> f_empty
    );

    // f_full and f_empty cannot be simultaneously asserted
    full_empty_mutex: assert property (
        @(posedge clock) !(f_full && f_empty)
    );

    // Counter never exceeds 15
    counter_max_bound: assert property (
        @(posedge clock) fifo.counter <= 4'd15
    );

    // Counter never underflows (stays >= 0, unsigned so just ensure no wrap from 0)
    counter_no_underflow: assert property (
        @(posedge clock) (!reset && f_empty && rd_en && !wr_en) |=> (fifo.counter == 4'd0)
    );

    // Counter no overflow: writing when full doesn't increase counter
    counter_no_overflow: assert property (
        @(posedge clock) (!reset && f_full && wr_en && !rd_en) |=> (fifo.counter == 4'd15)
    );

    // After reset, wr_ptr == 0
    reset_wr_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}})
    );

    // After reset, rd_ptr == 0
    reset_rd_ptr_zero: assert property (
        @(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}})
    );

    // After reset, counter == 0
    reset_counter_zero: assert property (
        @(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}})
    );

    // Write pointer increments on successful write
    wr_ptr_increments: assert property (
        @(posedge clock) (!reset && wr_en && !f_full) |=> (fifo.wr_ptr == ($past(fifo.wr_ptr) + 4'd1))
    );

    // Write pointer stable when not writing or full
    wr_ptr_stable: assert property (
        @(posedge clock) (!reset && (!wr_en || f_full)) |=> (fifo.wr_ptr == $past(fifo.wr_ptr))
    );

    // Read pointer increments on successful read
    rd_ptr_increments: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty) |=> (fifo.rd_ptr == ($past(fifo.rd_ptr) + 4'd1))
    );

    // Read pointer stable when not reading or empty
    rd_ptr_stable: assert property (
        @(posedge clock) (!reset && (!rd_en || f_empty)) |=> (fifo.rd_ptr == $past(fifo.rd_ptr))
    );

    // Counter increments on write-only (not full, not reading)
    counter_increments_on_write: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && !rd_en) |=> (fifo.counter == ($past(fifo.counter) + 4'd1))
    );

    // Counter decrements on read-only (not empty, not writing)
    counter_decrements_on_read: assert property (
        @(posedge clock) (!reset && rd_en && !f_empty && !wr_en) |=> (fifo.counter == ($past(fifo.counter) - 4'd1))
    );

    // Counter stable on simultaneous read and write (both valid)
    counter_stable_simultaneous_rw: assert property (
        @(posedge clock) (!reset && wr_en && !f_full && rd_en && !f_empty) |=> (fifo.counter == $past(fifo.counter))
    );

    // data_out always reflects mem[rd_ptr]
    data_out_reflects_mem: assert property (
        @(posedge clock) data_out == fifo.mem[fifo.rd_ptr]
    );

    // If FIFO is full and no read, it stays full
    full_stays_full: assert property (
        @(posedge clock) (!reset && f_full && !rd_en) |=> f_full
    );

    // If FIFO is empty and no write, it stays empty
    empty_stays_empty: assert property (
        @(posedge clock) (!reset && f_empty && !wr_en) |=> f_empty
    );

    // f_full deasserts after a successful read from full state
    full_deasserts_on_read: assert property (
        @(posedge clock) (!reset && f_full && rd_en && !wr_en) |=> !f_full
    );

    // f_empty deasserts after a successful write into empty FIFO
    empty_deasserts_on_write: assert property (
        @(posedge clock) (!reset && f_empty && wr_en && !rd_en) |=> !f_empty
    );

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
