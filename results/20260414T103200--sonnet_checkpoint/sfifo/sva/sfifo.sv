module sfifo_assert #(
    parameter DW     = 8,
    parameter LGFLEN = 4
) (
    input wire               i_clk,
    input wire               i_reset,
    input wire               i_wr,
    input wire [(DW-1):0]    i_data,
    input wire               o_full,
    input wire               i_rd,
    input wire [(DW-1):0]    o_data,
    input wire               o_empty,
    input wire               o_err
);

    localparam FLEN = (1 << LGFLEN);

    wire [LGFLEN:0] fifo_count;
    assign fifo_count = sfifo.wraddr - sfifo.rdaddr;

    // ----------------------------------------------------------------
    // Reset behaviour
    // ----------------------------------------------------------------
    reset_clears_empty_flag    : assert property (@(posedge i_clk) i_reset |=> o_empty);
    reset_clears_full_flag     : assert property (@(posedge i_clk) i_reset |=> !o_full);
    reset_zeroes_wraddr        : assert property (@(posedge i_clk) i_reset |=> sfifo.wraddr == '0);
    reset_zeroes_rdaddr        : assert property (@(posedge i_clk) i_reset |=> sfifo.rdaddr == '0);
    reset_clears_overflow_flag : assert property (@(posedge i_clk) i_reset |=> !sfifo.r_ovfl);
    reset_clears_underflow_flag: assert property (@(posedge i_clk) i_reset |=> !sfifo.r_unfl);

    // ----------------------------------------------------------------
    // w_wr / w_rd combinational definitions
    // ----------------------------------------------------------------
    w_wr_definition: assert property (@(posedge i_clk)
        sfifo.w_wr == (i_wr && (!o_full || i_rd)));

    w_rd_definition: assert property (@(posedge i_clk)
        sfifo.w_rd == (i_rd && !o_empty));

    // ----------------------------------------------------------------
    // FIFO count invariants
    // ----------------------------------------------------------------
    count_never_exceeds_flen: assert property (@(posedge i_clk)
        disable iff (i_reset) fifo_count <= FLEN);

    empty_iff_addrs_equal: assert property (@(posedge i_clk)
        disable iff (i_reset) o_empty == (sfifo.wraddr == sfifo.rdaddr));

    full_iff_count_equals_flen: assert property (@(posedge i_clk)
        disable iff (i_reset) o_full == (fifo_count == FLEN));

    empty_means_count_zero: assert property (@(posedge i_clk)
        disable iff (i_reset) o_empty |-> fifo_count == '0);

    full_means_count_is_flen: assert property (@(posedge i_clk)
        disable iff (i_reset) o_full |-> fifo_count == FLEN);

    not_simultaneously_full_and_empty: assert property (@(posedge i_clk)
        disable iff (i_reset) !(o_full && o_empty));

    // ----------------------------------------------------------------
    // Write pointer behaviour
    // ----------------------------------------------------------------
    wraddr_increments_on_write: assert property (@(posedge i_clk)
        disable iff (i_reset) sfifo.w_wr |=>
            sfifo.wraddr == ($past(sfifo.wraddr) + 1'b1));

    wraddr_stable_when_no_write: assert property (@(posedge i_clk)
        disable iff (i_reset) !sfifo.w_wr |=>
            sfifo.wraddr == $past(sfifo.wraddr));

    // ----------------------------------------------------------------
    // Read pointer behaviour
    // ----------------------------------------------------------------
    rdaddr_increments_on_read: assert property (@(posedge i_clk)
        disable iff (i_reset) sfifo.w_rd |=>
            sfifo.rdaddr == ($past(sfifo.rdaddr) + 1'b1));

    rdaddr_stable_when_no_read: assert property (@(posedge i_clk)
        disable iff (i_reset) !sfifo.w_rd |=>
            sfifo.rdaddr == $past(sfifo.rdaddr));

    // ----------------------------------------------------------------
    // Count evolution
    // ----------------------------------------------------------------
    write_only_increments_count: assert property (@(posedge i_clk)
        disable iff (i_reset) (sfifo.w_wr && !sfifo.w_rd) |=>
            fifo_count == ($past(fifo_count) + 1'b1));

    read_only_decrements_count: assert property (@(posedge i_clk)
        disable iff (i_reset) (!sfifo.w_wr && sfifo.w_rd) |=>
            fifo_count == ($past(fifo_count) - 1'b1));

    simultaneous_read_write_preserves_count: assert property (@(posedge i_clk)
        disable iff (i_reset) (sfifo.w_wr && sfifo.w_rd) |=>
            fifo_count == $past(fifo_count));

    no_operation_preserves_count: assert property (@(posedge i_clk)
        disable iff (i_reset) (!sfifo.w_wr && !sfifo.w_rd) |=>
            fifo_count == $past(fifo_count));

    // ----------------------------------------------------------------
    // Gate conditions
    // ----------------------------------------------------------------
    no_effective_write_when_full_and_no_read: assert property (@(posedge i_clk)
        disable iff (i_reset) (o_full && !i_rd) |-> !sfifo.w_wr);

    no_effective_read_when_empty: assert property (@(posedge i_clk)
        disable iff (i_reset) o_empty |-> !sfifo.w_rd);

    // ----------------------------------------------------------------
    // Error flag behaviour
    // ----------------------------------------------------------------
    overflow_flag_is_sticky: assert property (@(posedge i_clk)
        disable iff (i_reset) sfifo.r_ovfl |=> sfifo.r_ovfl);

    underflow_flag_is_sticky: assert property (@(posedge i_clk)
        disable iff (i_reset) sfifo.r_unfl |=> sfifo.r_unfl);

    overflow_set_on_write_to_full_fifo: assert property (@(posedge i_clk)
        disable iff (i_reset) (o_full && i_wr && !i_rd) |=>
            sfifo.r_ovfl);

    underflow_set_on_read_from_empty_fifo: assert property (@(posedge i_clk)
        disable iff (i_reset) (o_empty && i_rd) |=>
            sfifo.r_unfl);

    overflow_not_set_on_valid_write: assert property (@(posedge i_clk)
        disable iff (i_reset) (!o_full && i_wr) |=>
            sfifo.r_ovfl == $past(sfifo.r_ovfl));

    underflow_not_set_on_valid_read: assert property (@(posedge i_clk)
        disable iff (i_reset) (!o_empty && i_rd) |=>
            sfifo.r_unfl == $past(sfifo.r_unfl));

    // ----------------------------------------------------------------
    // o_err combinational definition
    // ----------------------------------------------------------------
    err_equals_ovfl_or_unfl: assert property (@(posedge i_clk)
        o_err == (sfifo.r_ovfl || sfifo.r_unfl));

    // ----------------------------------------------------------------
    // o_full next-state transitions
    // ----------------------------------------------------------------
    full_cleared_by_rd_without_wr: assert property (@(posedge i_clk)
        disable iff (i_reset) (o_full && i_rd && !i_wr) |=> !o_full);

    full_preserved_by_rd_with_wr: assert property (@(posedge i_clk)
        disable iff (i_reset) (o_full && i_rd && i_wr) |=> o_full);

    // ----------------------------------------------------------------
    // o_empty next-state transitions
    // ----------------------------------------------------------------
    empty_cleared_by_wr: assert property (@(posedge i_clk)
        disable iff (i_reset) (i_wr) |=> !o_empty);

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
