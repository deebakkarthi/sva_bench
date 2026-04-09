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

  // --- Reset behavior ---
  reset_clears_wr_ptr  : assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.wr_ptr == 0);
  reset_clears_rd_ptr  : assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.rd_ptr == 0);
  reset_clears_count   : assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.count == 0);

  // --- Status flag correctness ---
  full_flag_reflects_count  : assert property (@(posedge i_clk) o_full  == (fifo_sync.count == NUM_ELEM - 1));
  empty_flag_reflects_count : assert property (@(posedge i_clk) o_empty == (fifo_sync.count == 0));

  // --- Mutual exclusion of full and empty ---
  no_simultaneous_full_and_empty : assert property (@(posedge i_clk) !(o_full && o_empty));

  // --- Count bounds ---
  count_never_underflows : assert property (@(posedge i_clk) fifo_sync.count >= 0);
  count_never_overflows  : assert property (@(posedge i_clk) fifo_sync.count <= NUM_ELEM - 1);

  // --- Count transitions on write-only (not full) ---
  count_increments_on_write : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && !i_rd_en && !o_full) |=> fifo_sync.count == $past(fifo_sync.count) + 1
  );

  // --- Count transitions on read-only (not empty) ---
  count_decrements_on_read : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_rd_en && !i_wr_en && !o_empty) |=> fifo_sync.count == $past(fifo_sync.count) - 1
  );

  // --- Count stable when writing to full FIFO ---
  count_stable_on_write_when_full : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && !i_rd_en && o_full) |=> fifo_sync.count == $past(fifo_sync.count)
  );

  // --- Count stable when reading from empty FIFO ---
  count_stable_on_read_when_empty : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_rd_en && !i_wr_en && o_empty) |=> fifo_sync.count == $past(fifo_sync.count)
  );

  // --- Count stable on simultaneous read and write ---
  count_stable_on_simultaneous_rd_wr : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && i_rd_en) |=> fifo_sync.count == $past(fifo_sync.count)
  );

  // --- Count stable on no operation ---
  count_stable_on_no_op : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (!i_wr_en && !i_rd_en) |=> fifo_sync.count == $past(fifo_sync.count)
  );

  // --- Write pointer increments on successful write ---
  wr_ptr_increments_on_successful_write : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && !i_rd_en && !o_full) |=> fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr) + 1
  );

  // --- Write pointer stable when write is suppressed (full) ---
  wr_ptr_stable_when_full : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && !i_rd_en && o_full) |=> fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr)
  );

  // --- Write pointer stable when no write ---
  wr_ptr_stable_on_no_write : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !i_wr_en |=> fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr)
  );

  // --- Read pointer increments on successful read ---
  rd_ptr_increments_on_successful_read : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_rd_en && !i_wr_en && !o_empty) |=> fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr) + 1
  );

  // --- Read pointer stable when read is suppressed (empty) ---
  rd_ptr_stable_when_empty : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_rd_en && !i_wr_en && o_empty) |=> fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr)
  );

  // --- Read pointer stable when no read ---
  rd_ptr_stable_on_no_read : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !i_rd_en |=> fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr)
  );

  // --- o_empty deasserts after a successful write into empty FIFO ---
  empty_deasserts_after_write : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_wr_en && !i_rd_en && o_empty) |=> !o_empty
  );

  // --- o_full deasserts after a successful read from full FIFO ---
  full_deasserts_after_read : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_rd_en && !i_wr_en && o_full) |=> !o_full
  );

endmodule

bind fifo_sync fifo_sync_assert fifo_sync_assert_instance (.*);
