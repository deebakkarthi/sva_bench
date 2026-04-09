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

  // ---------------------------------------------------------------
  // Reset behaviour
  // ---------------------------------------------------------------
  reset_clears_wr_ptr : assert property (
      @(posedge i_clk) !i_rst_n |=> (fifo_sync.wr_ptr == '0));

  reset_clears_rd_ptr : assert property (
      @(posedge i_clk) !i_rst_n |=> (fifo_sync.rd_ptr == '0));

  reset_clears_count : assert property (
      @(posedge i_clk) !i_rst_n |=> (fifo_sync.count == '0));

  reset_asserts_empty : assert property (
      @(posedge i_clk) !i_rst_n |=> o_empty);

  reset_deasserts_full : assert property (
      @(posedge i_clk) !i_rst_n |=> !o_full);

  // ---------------------------------------------------------------
  // o_empty / o_full flag correctness
  // ---------------------------------------------------------------
  empty_iff_count_zero : assert property (
      @(posedge i_clk) i_rst_n |-> (o_empty == (fifo_sync.count == '0)));

  full_iff_count_max : assert property (
      @(posedge i_clk) i_rst_n |-> (o_full == (fifo_sync.count == NUM_ELEM - 1)));

  not_full_and_empty_simultaneously : assert property (
      @(posedge i_clk) i_rst_n |-> !(o_full && o_empty));

  // ---------------------------------------------------------------
  // Count never overflows or underflows
  // ---------------------------------------------------------------
  count_never_exceeds_max : assert property (
      @(posedge i_clk) i_rst_n |-> fifo_sync.count <= NUM_ELEM - 1);

  count_never_decrements_when_zero : assert property (
      @(posedge i_clk) i_rst_n && (fifo_sync.count == '0) |->
          !(i_rd_en && !i_wr_en));

  count_never_increments_when_full : assert property (
      @(posedge i_clk) i_rst_n && o_full |->
          !(i_wr_en && !i_rd_en));

  // ---------------------------------------------------------------
  // Write path: write-only, not full
  // ---------------------------------------------------------------
  write_only_not_full_increments_wr_ptr : assert property (
      @(posedge i_clk)
      i_rst_n && i_wr_en && !i_rd_en && !o_full
      |=> (fifo_sync.wr_ptr == ($past(fifo_sync.wr_ptr) + 1'b1)));

  write_only_not_full_increments_count : assert property (
      @(posedge i_clk)
      i_rst_n && i_wr_en && !i_rd_en && !o_full
      |=> (fifo_sync.count == ($past(fifo_sync.count) + 1'b1)));

  write_only_not_full_rd_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_wr_en && !i_rd_en && !o_full
      |=> (fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr)));

  // ---------------------------------------------------------------
  // Write path: write-only, full → FIFO ignores the write
  // ---------------------------------------------------------------
  write_only_full_wr_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_wr_en && !i_rd_en && o_full
      |=> (fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr)));

  write_only_full_count_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_wr_en && !i_rd_en && o_full
      |=> (fifo_sync.count == $past(fifo_sync.count)));

  // ---------------------------------------------------------------
  // Read path: read-only, not empty
  // ---------------------------------------------------------------
  read_only_not_empty_increments_rd_ptr : assert property (
      @(posedge i_clk)
      i_rst_n && i_rd_en && !i_wr_en && !o_empty
      |=> (fifo_sync.rd_ptr == ($past(fifo_sync.rd_ptr) + 1'b1)));

  read_only_not_empty_decrements_count : assert property (
      @(posedge i_clk)
      i_rst_n && i_rd_en && !i_wr_en && !o_empty
      |=> (fifo_sync.count == ($past(fifo_sync.count) - 1'b1)));

  read_only_not_empty_wr_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_rd_en && !i_wr_en && !o_empty
      |=> (fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr)));

  // ---------------------------------------------------------------
  // Read path: read-only, empty → FIFO ignores the read
  // ---------------------------------------------------------------
  read_only_empty_rd_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_rd_en && !i_wr_en && o_empty
      |=> (fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr)));

  read_only_empty_count_stable : assert property (
      @(posedge i_clk)
      i_rst_n && i_rd_en && !i_wr_en && o_empty
      |=> (fifo_sync.count == $past(fifo_sync.count)));

  // ---------------------------------------------------------------
  // No-op: neither read nor write → all pointers and count stable
  // ---------------------------------------------------------------
  no_op_wr_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && !i_wr_en && !i_rd_en
      |=> (fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr)));

  no_op_rd_ptr_stable : assert property (
      @(posedge i_clk)
      i_rst_n && !i_wr_en && !i_rd_en
      |=> (fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr)));

  no_op_count_stable : assert property (
      @(posedge i_clk)
      i_rst_n && !i_wr_en && !i_rd_en
      |=> (fifo_sync.count == $past(fifo_sync.count)));

endmodule

bind fifo_sync fifo_sync_assert fifo_sync_assert_instance (.*);
