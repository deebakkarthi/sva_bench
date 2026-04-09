module fifo_sync_assert #(
    parameter int NUM_ELEM = 8,
    parameter int DWIDTH   = 16
) (
    input wire i_clk,
    input wire i_rst_n,
    input wire i_wr_en,
    input wire i_rd_en,
    input wire [DWIDTH-1:0] i_data,
    input wire [DWIDTH-1:0] o_data,
    input wire o_full,
    input wire o_empty
);

    full_flag_correct: assert property (
        @(posedge i_clk) o_full == (fifo_sync.count == NUM_ELEM - 1)
    );

    empty_flag_correct: assert property (
        @(posedge i_clk) o_empty == (fifo_sync.count == 0)
    );

    full_and_empty_mutually_exclusive: assert property (
        @(posedge i_clk) !(o_full && o_empty)
    );

    reset_clears_wr_ptr: assert property (
        @(posedge i_clk) !i_rst_n |=> (fifo_sync.wr_ptr == 0)
    );

    reset_clears_rd_ptr: assert property (
        @(posedge i_clk) !i_rst_n |=> (fifo_sync.rd_ptr == 0)
    );

    reset_clears_count: assert property (
        @(posedge i_clk) !i_rst_n |=> (fifo_sync.count == 0)
    );

    reset_implies_empty: assert property (
        @(posedge i_clk) !i_rst_n |=> o_empty
    );

    reset_implies_not_full: assert property (
        @(posedge i_clk) !i_rst_n |=> !o_full
    );

    count_increments_on_valid_write: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_wr_en && !i_rd_en && !o_full) |=> (fifo_sync.count == $past(fifo_sync.count) + 1)
    );

    count_decrements_on_valid_read: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_rd_en && !i_wr_en && !o_empty) |=> (fifo_sync.count == $past(fifo_sync.count) - 1)
    );

    count_stable_when_both_rw_active: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_wr_en && i_rd_en) |=> (fifo_sync.count == $past(fifo_sync.count))
    );

    count_stable_when_no_rw_active: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (!i_wr_en && !i_rd_en) |=> (fifo_sync.count == $past(fifo_sync.count))
    );

    count_stable_on_write_when_full: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_wr_en && !i_rd_en && o_full) |=> (fifo_sync.count == $past(fifo_sync.count))
    );

    count_stable_on_read_when_empty: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_rd_en && !i_wr_en && o_empty) |=> (fifo_sync.count == $past(fifo_sync.count))
    );

    count_never_exceeds_max: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        fifo_sync.count <= (NUM_ELEM - 1)
    );

    wr_ptr_increments_on_valid_write: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_wr_en && !i_rd_en && !o_full) |=> (fifo_sync.wr_ptr == ($past(fifo_sync.wr_ptr) + 1))
    );

    rd_ptr_increments_on_valid_read: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_rd_en && !i_wr_en && !o_empty) |=> (fifo_sync.rd_ptr == ($past(fifo_sync.rd_ptr) + 1))
    );

    wr_ptr_stable_when_no_valid_write: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (!i_wr_en || i_rd_en || o_full) |=> (fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr))
    );

    rd_ptr_stable_when_no_valid_read: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (!i_rd_en || i_wr_en || o_empty) |=> (fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr))
    );

    data_written_to_correct_slot: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_wr_en && !i_rd_en && !o_full) |=> (fifo_sync.fifo[$past(fifo_sync.wr_ptr)] == $past(i_data[0]))
    );

    output_data_reflects_fifo_rd_slot: assert property (
        @(posedge i_clk) disable iff (!i_rst_n)
        (i_rd_en && !i_wr_en && !o_empty) |=> (o_data == $past(fifo_sync.fifo[$past(fifo_sync.rd_ptr)]))
    );

    empty_when_count_zero: assert property (
        @(posedge i_clk) (fifo_sync.count == 0) |-> o_empty
    );

    full_when_count_max: assert property (
        @(posedge i_clk) (fifo_sync.count == NUM_ELEM - 1) |-> o_full
    );

    not_empty_when_count_nonzero: assert property (
        @(posedge i_clk) (fifo_sync.count != 0) |-> !o_empty
    );

    not_full_when_count_below_max: assert property (
        @(posedge i_clk) (fifo_sync.count < NUM_ELEM - 1) |-> !o_full
    );

endmodule

bind fifo_sync fifo_sync_assert fifo_sync_assert_instance (.*);
