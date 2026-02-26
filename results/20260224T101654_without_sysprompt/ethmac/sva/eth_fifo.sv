module eth_fifo_assert #(
    parameter DATA_WIDTH = 32,
    parameter DEPTH      = 8,
    parameter CNT_WIDTH  = 4
)(
    input                    clk,
    input                    reset,
    input                    write,
    input                    read,
    input                    clear,
    input  [DATA_WIDTH-1:0]  data_in,
    output [DATA_WIDTH-1:0]  data_out,
    output                   almost_full,
    output                   full,
    output                   almost_empty,
    output                   empty,
    output [CNT_WIDTH-1:0]   cnt
);

    // After reset, cnt must be zero
    cnt_reset_zero : assert property (
        @(posedge clk) $rose(reset) |=> (cnt == 0)
    );

    // After reset, empty must be asserted
    empty_after_reset : assert property (
        @(posedge clk) $rose(reset) |=> empty
    );

    // After reset, full must be deasserted
    full_deasserted_after_reset : assert property (
        @(posedge clk) $rose(reset) |=> !full
    );

    // empty is true iff cnt == 0
    empty_iff_cnt_zero : assert property (
        @(posedge clk) disable iff (reset)
        empty == (cnt == 0)
    );

    // almost_empty is true iff cnt == 1
    almost_empty_iff_cnt_one : assert property (
        @(posedge clk) disable iff (reset)
        almost_empty == (cnt == 1)
    );

    // full is true iff cnt == DEPTH
    full_iff_cnt_depth : assert property (
        @(posedge clk) disable iff (reset)
        full == (cnt == DEPTH)
    );

    // almost_full is true iff cnt[CNT_WIDTH-2:0] are all ones
    almost_full_correct : assert property (
        @(posedge clk) disable iff (reset)
        almost_full == (&cnt[CNT_WIDTH-2:0])
    );

    // cnt never exceeds DEPTH
    cnt_never_exceeds_depth : assert property (
        @(posedge clk) disable iff (reset)
        cnt <= DEPTH
    );

    // full and empty are mutually exclusive (DEPTH > 1)
    full_and_empty_mutually_exclusive : assert property (
        @(posedge clk) disable iff (reset)
        !(full && empty)
    );

    // On write only (no read, no clear, not full), cnt increments by 1
    cnt_increments_on_write : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && write && !read && !full) |=> (cnt == $past(cnt) + 1)
    );

    // On read only (no write, no clear, not empty), cnt decrements by 1
    cnt_decrements_on_read : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && read && !write && !empty) |=> (cnt == $past(cnt) - 1)
    );

    // On simultaneous read and write (no clear), cnt remains stable
    cnt_stable_on_read_write : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && read && write) |=> (cnt == $past(cnt))
    );

    // On no read and no write (no clear), cnt remains stable
    cnt_stable_on_no_rw : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && !read && !write) |=> (cnt == $past(cnt))
    );

    // On clear with write only (read=0), cnt becomes 1
    cnt_clear_write_only : assert property (
        @(posedge clk) disable iff (reset)
        (clear && write && !read) |=> (cnt == 1)
    );

    // On clear with read only (write=0), cnt becomes 1
    cnt_clear_read_only : assert property (
        @(posedge clk) disable iff (reset)
        (clear && read && !write) |=> (cnt == 1)
    );

    // On clear with both read and write, cnt becomes 0
    cnt_clear_both_rw : assert property (
        @(posedge clk) disable iff (reset)
        (clear && read && write) |=> (cnt == 0)
    );

    // On clear with neither read nor write, cnt becomes 0
    cnt_clear_no_rw : assert property (
        @(posedge clk) disable iff (reset)
        (clear && !read && !write) |=> (cnt == 0)
    );

    // When full, write does not advance write_pointer
    write_pointer_stable_when_full : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && write && full) |=> ($past(write_pointer) == write_pointer - 0)
    );

    // When empty, read does not advance read_pointer
    read_pointer_stable_when_empty : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && read && empty) |=> ($past(read_pointer) == read_pointer - 0)
    );

    // Write pointer increments on valid write
    write_pointer_increments : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && write && !full) |=> (write_pointer == ($past(write_pointer) + 1'b1))
    );

    // Read pointer increments on valid read
    read_pointer_increments : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && read && !empty) |=> (read_pointer == ($past(read_pointer) + 1'b1))
    );

    // After reset, write_pointer is 0
    write_pointer_reset_zero : assert property (
        @(posedge clk) $rose(reset) |=> (write_pointer == 0)
    );

    // After reset, read_pointer is 0
    read_pointer_reset_zero : assert property (
        @(posedge clk) $rose(reset) |=> (read_pointer == 0)
    );

    // almost_full implies not empty
    almost_full_implies_not_empty : assert property (
        @(posedge clk) disable iff (reset)
        almost_full |-> !empty
    );

    // almost_empty implies not full
    almost_empty_implies_not_full : assert property (
        @(posedge clk) disable iff (reset)
        almost_empty |-> !full
    );

    // full implies not empty
    full_implies_not_empty : assert property (
        @(posedge clk) disable iff (reset)
        full |-> !empty
    );

    // empty implies not full
    empty_implies_not_full : assert property (
        @(posedge clk) disable iff (reset)
        empty |-> !full
    );

    // cnt stays 0 on read when already empty (no clear, no write)
    cnt_no_underflow : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && !write && read && empty) |=> (cnt == 0)
    );

    // cnt stays DEPTH on write when already full (no clear, no read)
    cnt_no_overflow : assert property (
        @(posedge clk) disable iff (reset)
        (!clear && write && !read && full) |=> (cnt == DEPTH)
    );

endmodule

bind eth_fifo eth_fifo_assert #(
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH),
    .CNT_WIDTH(CNT_WIDTH)
) eth_fifo_assert_instance (.*);
