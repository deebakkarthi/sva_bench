module sfifo_assert #(
    parameter   DW     = 8,
    parameter   LGFLEN = 4
) (
    input wire              i_clk,
    input wire              i_reset,
    input wire              i_wr,
    input wire [(DW-1):0]   i_data,
    input wire              o_full,
    input wire              i_rd,
    input wire [(DW-1):0]   o_data,
    input wire              o_empty,
    input wire              o_err
);

localparam FLEN = (1 << LGFLEN);

// Reset behavior
reset_clears_wraddr      : assert property (@(posedge i_clk) i_reset |=> (sfifo.wraddr == 0));
reset_clears_rdaddr      : assert property (@(posedge i_clk) i_reset |=> (sfifo.rdaddr == 0));
reset_sets_o_empty       : assert property (@(posedge i_clk) i_reset |=> o_empty);
reset_clears_o_full      : assert property (@(posedge i_clk) i_reset |=> !o_full);
reset_clears_r_ovfl      : assert property (@(posedge i_clk) i_reset |=> !sfifo.r_ovfl);
reset_clears_r_unfl      : assert property (@(posedge i_clk) i_reset |=> !sfifo.r_unfl);

// o_err is the combinational OR of the two sticky error flags
err_is_ovfl_or_unfl      : assert property (@(posedge i_clk) o_err == (sfifo.r_ovfl || sfifo.r_unfl));

// Internal enable signal definitions
w_wr_def                 : assert property (@(posedge i_clk) sfifo.w_wr == (i_wr && (!o_full || i_rd)));
w_rd_def                 : assert property (@(posedge i_clk) sfifo.w_rd == (i_rd && !o_empty));

// Structural invariants relating pointers to status flags
empty_iff_ptrs_equal     : assert property (@(posedge i_clk) o_empty == (sfifo.wraddr == sfifo.rdaddr));
full_iff_ptrs_flen_apart : assert property (@(posedge i_clk)
    o_full == ((sfifo.wraddr[LGFLEN] != sfifo.rdaddr[LGFLEN]) &&
               (sfifo.wraddr[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0])));
full_empty_mutex         : assert property (@(posedge i_clk) !(o_full && o_empty));
fill_bounded_by_flen     : assert property (@(posedge i_clk)
    (sfifo.wraddr - sfifo.rdaddr) <= (LGFLEN+1)'(FLEN));

// Write pointer update behavior
wraddr_inc_on_w_wr       : assert property (@(posedge i_clk)
    (!i_reset && sfifo.w_wr) |=> (sfifo.wraddr == $past(sfifo.wraddr) + 1'b1));
wraddr_stable_no_w_wr    : assert property (@(posedge i_clk)
    (!i_reset && !sfifo.w_wr) ##1 !i_reset |-> (sfifo.wraddr == $past(sfifo.wraddr)));

// Read pointer update behavior
rdaddr_inc_on_w_rd       : assert property (@(posedge i_clk)
    (!i_reset && sfifo.w_rd) |=> (sfifo.rdaddr == $past(sfifo.rdaddr) + 1'b1));
rdaddr_stable_no_w_rd    : assert property (@(posedge i_clk)
    (!i_reset && !sfifo.w_rd) ##1 !i_reset |-> (sfifo.rdaddr == $past(sfifo.rdaddr)));

// Overflow flag: set when write is attempted on full FIFO without simultaneous read
overflow_sets_flag       : assert property (@(posedge i_clk)
    (!i_reset && i_wr && o_full && !i_rd) |=> sfifo.r_ovfl);

// Underflow flag: set when read is attempted on empty FIFO
underflow_sets_flag      : assert property (@(posedge i_clk)
    (!i_reset && i_rd && o_empty) |=> sfifo.r_unfl);

// Error flags are sticky (only cleared by reset)
ovfl_flag_sticky         : assert property (@(posedge i_clk)
    (!i_reset && sfifo.r_ovfl) |=> sfifo.r_ovfl);
unfl_flag_sticky         : assert property (@(posedge i_clk)
    (!i_reset && sfifo.r_unfl) |=> sfifo.r_unfl);

// Full flag transitions
full_clears_on_read_only : assert property (@(posedge i_clk)
    (!i_reset && o_full && i_rd && !i_wr) |=> !o_full);
full_stable_on_rd_and_wr : assert property (@(posedge i_clk)
    (!i_reset && o_full && i_rd && i_wr) |=> o_full);
full_set_on_last_entry   : assert property (@(posedge i_clk)
    (!i_reset && !o_full && i_wr && !i_rd &&
     sfifo.w_wraddr_plus_one[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0] &&
     sfifo.w_wraddr_plus_one[LGFLEN] != sfifo.rdaddr[LGFLEN]) |=> o_full);

// Empty flag transitions
empty_clears_on_write    : assert property (@(posedge i_clk)
    (!i_reset && o_empty && i_wr) |=> !o_empty);
empty_set_on_last_read   : assert property (@(posedge i_clk)
    (!i_reset && !o_empty && i_rd && !i_wr &&
     sfifo.w_rdaddr_plus_one == sfifo.wraddr) |=> o_empty);

// o_data continuously reflects FIFO memory at current read pointer
o_data_is_fifo_at_rdptr  : assert property (@(posedge i_clk)
    o_data == sfifo.fifo[sfifo.rdaddr[LGFLEN-1:0]]);

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
