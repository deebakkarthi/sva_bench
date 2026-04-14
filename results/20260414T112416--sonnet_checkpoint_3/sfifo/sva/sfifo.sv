module sfifo_assert #(
    parameter DW = 8,
    parameter LGFLEN = 4
) (
    input wire i_clk,
    input wire i_reset,
    input wire i_wr,
    input wire [(DW-1):0] i_data,
    input wire o_full,
    input wire i_rd,
    input wire [(DW-1):0] o_data,
    input wire o_empty,
    input wire o_err
);

    // Reset behavior
    reset_clears_full:   assert property (@(posedge i_clk) i_reset |=> !o_full);
    reset_sets_empty:    assert property (@(posedge i_clk) i_reset |=> o_empty);
    reset_clears_wraddr: assert property (@(posedge i_clk) i_reset |=> (sfifo.wraddr == 0));
    reset_clears_rdaddr: assert property (@(posedge i_clk) i_reset |=> (sfifo.rdaddr == 0));
    reset_clears_ovfl:   assert property (@(posedge i_clk) i_reset |=> !sfifo.r_ovfl);
    reset_clears_unfl:   assert property (@(posedge i_clk) i_reset |=> !sfifo.r_unfl);

    // Structural invariants (combinational)
    full_and_empty_mutex:    assert property (@(posedge i_clk) !(o_full && o_empty));
    err_equals_ovfl_or_unfl: assert property (@(posedge i_clk) o_err == (sfifo.r_ovfl || sfifo.r_unfl));
    output_data_matches_fifo: assert property (@(posedge i_clk) o_data == sfifo.fifo[sfifo.rdaddr[LGFLEN-1:0]]);

    // Pointer-based full/empty invariants
    empty_iff_ptrs_equal: assert property (@(posedge i_clk)
        disable iff (i_reset)
        o_empty == (sfifo.wraddr == sfifo.rdaddr));

    full_iff_ptr_wrap: assert property (@(posedge i_clk)
        disable iff (i_reset)
        o_full == ((sfifo.wraddr[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0]) &&
                   (sfifo.wraddr[LGFLEN] != sfifo.rdaddr[LGFLEN])));

    // FIFO occupancy bounds
    fifo_count_in_range: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (sfifo.wraddr - sfifo.rdaddr) <= (1 << LGFLEN));

    full_implies_max_count: assert property (@(posedge i_clk)
        disable iff (i_reset)
        o_full |-> ((sfifo.wraddr - sfifo.rdaddr) == (1 << LGFLEN)));

    empty_implies_zero_count: assert property (@(posedge i_clk)
        disable iff (i_reset)
        o_empty |-> (sfifo.wraddr == sfifo.rdaddr));

    // Write pointer updates
    wraddr_increments_on_valid_write: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_wr && (i_rd || !o_full)) |=> (sfifo.wraddr == ($past(sfifo.wraddr) + 1'b1)));

    wraddr_stable_without_valid_write: assert property (@(posedge i_clk)
        disable iff (i_reset)
        !(i_wr && (i_rd || !o_full)) |=> (sfifo.wraddr == $past(sfifo.wraddr)));

    // Read pointer updates
    rdaddr_increments_on_valid_read: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_rd && !o_empty) |=> (sfifo.rdaddr == ($past(sfifo.rdaddr) + 1'b1)));

    rdaddr_stable_without_valid_read: assert property (@(posedge i_clk)
        disable iff (i_reset)
        !(i_rd && !o_empty) |=> (sfifo.rdaddr == $past(sfifo.rdaddr)));

    // Overflow/underflow flag assertion
    overflow_on_full_write: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_wr && o_full && !i_rd) |=> sfifo.r_ovfl);

    underflow_on_empty_read: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_rd && o_empty) |=> sfifo.r_unfl);

    // Sticky error flags
    ovfl_flag_sticky: assert property (@(posedge i_clk)
        disable iff (i_reset)
        sfifo.r_ovfl |=> sfifo.r_ovfl);

    unfl_flag_sticky: assert property (@(posedge i_clk)
        disable iff (i_reset)
        sfifo.r_unfl |=> sfifo.r_unfl);

    // No overflow error if read is simultaneous with full write
    no_overflow_on_full_write_with_read: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_wr && o_full && i_rd) |=> !$rose(sfifo.r_ovfl));

    // No underflow error if write is simultaneous with empty read
    no_underflow_on_empty_read_with_write: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_rd && o_empty && i_wr) |=> !$rose(sfifo.r_unfl));

    // Write to FIFO memory only on actual write
    fifo_written_on_w_wr: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (i_wr && (i_rd || !o_full)) |=>
        (sfifo.fifo[$past(sfifo.wraddr[LGFLEN-1:0])] == $past(i_data)));

    // o_full de-asserts after a read with no write
    full_clears_on_rd_no_wr: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (o_full && i_rd && !i_wr) |=> !o_full);

    // o_empty de-asserts after a write
    empty_clears_on_wr: assert property (@(posedge i_clk)
        disable iff (i_reset)
        (o_empty && i_wr) |=> !o_empty);

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
