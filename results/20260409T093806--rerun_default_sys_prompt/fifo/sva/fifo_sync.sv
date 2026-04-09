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

  reset_clears_wr_ptr:    assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.wr_ptr == 0);
  reset_clears_rd_ptr:    assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.rd_ptr == 0);
  reset_clears_count:     assert property (@(posedge i_clk) !i_rst_n |=> fifo_sync.count == 0);
  reset_asserts_empty:    assert property (@(posedge i_clk) !i_rst_n |=> o_empty);
  reset_deasserts_full:   assert property (@(posedge i_clk) !i_rst_n |=> !o_full);

  empty_iff_count_zero:   assert property (@(posedge i_clk) i_rst_n |-> (o_empty == (fifo_sync.count == 0)));
  full_iff_count_max:     assert property (@(posedge i_clk) i_rst_n |-> (o_full  == (fifo_sync.count == NUM_ELEM - 1)));

  count_never_exceeds_max:          assert property (@(posedge i_clk) fifo_sync.count <= NUM_ELEM - 1);
  full_and_empty_mutually_exclusive: assert property (@(posedge i_clk) !(o_full && o_empty));

  write_increments_count:   assert property (@(posedge i_clk)
    (i_rst_n && i_wr_en && !i_rd_en && !o_full) |=>
    fifo_sync.count == $past(fifo_sync.count) + 1);

  read_decrements_count:    assert property (@(posedge i_clk)
    (i_rst_n && i_rd_en && !i_wr_en && !o_empty) |=>
    fifo_sync.count == $past(fifo_sync.count) - 1);

  no_op_count_stable:       assert property (@(posedge i_clk)
    (i_rst_n && !i_wr_en && !i_rd_en) |=>
    fifo_sync.count == $past(fifo_sync.count));

  write_when_full_count_stable:  assert property (@(posedge i_clk)
    (i_rst_n && i_wr_en && !i_rd_en && o_full) |=>
    fifo_sync.count == $past(fifo_sync.count));

  read_when_empty_count_stable:  assert property (@(posedge i_clk)
    (i_rst_n && i_rd_en && !i_wr_en && o_empty) |=>
    fifo_sync.count == $past(fifo_sync.count));

  write_ptr_increments_on_valid_write: assert property (@(posedge i_clk)
    (i_rst_n && i_wr_en && !i_rd_en && !o_full) |=>
    fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr) + 1);

  read_ptr_increments_on_valid_read:   assert property (@(posedge i_clk)
    (i_rst_n && i_rd_en && !i_wr_en && !o_empty) |=>
    fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr) + 1);

  write_ptr_stable_when_no_write:      assert property (@(posedge i_clk)
    (i_rst_n && !(i_wr_en && !i_rd_en && !o_full)) |=>
    fifo_sync.wr_ptr == $past(fifo_sync.wr_ptr));

  read_ptr_stable_when_no_read:        assert property (@(posedge i_clk)
    (i_rst_n && !(i_rd_en && !i_wr_en && !o_empty)) |=>
    fifo_sync.rd_ptr == $past(fifo_sync.rd_ptr));

  no_write_when_full:   assert property (@(posedge i_clk)
    (i_rst_n && o_full && i_wr_en && !i_rd_en) |=>
    o_full);

  no_read_when_empty:   assert property (@(posedge i_clk)
    (i_rst_n && o_empty && i_rd_en && !i_wr_en) |=>
    o_empty);

endmodule

bind fifo_sync fifo_sync_assert #(.NUM_ELEM(NUM_ELEM), .DWIDTH(DWIDTH)) fifo_sync_assert_instance (.*);
