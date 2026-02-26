module fifo_sva
#(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 4
)
(
    input              clock,
    input              reset,
    input              wr_en,
    input              rd_en,
    input  [DWIDTH-1:0] data_in,
    input               f_full,
    input               f_empty,
    input  [DWIDTH-1:0] data_out,
    // internal signals exposed via bind
    input  [AWIDTH-1:0] wr_ptr,
    input  [AWIDTH-1:0] rd_ptr,
    input  [AWIDTH-1:0] counter
);

  // -----------------------------------------------------------------------
  // f_full: asserted when counter == 2^AWIDTH - 1
  // -----------------------------------------------------------------------
  ap_full_condition: assert property (@(posedge clock)
    !reset |-> (f_full == (counter == {AWIDTH{1'b1}}))
  );

  // -----------------------------------------------------------------------
  // f_empty: asserted when counter == 0
  // -----------------------------------------------------------------------
  ap_empty_condition: assert property (@(posedge clock)
    !reset |-> (f_empty == (counter == {AWIDTH{1'b0}}))
  );

  // -----------------------------------------------------------------------
  // f_full and f_empty are mutually exclusive
  // -----------------------------------------------------------------------
  ap_full_empty_mutex: assert property (@(posedge clock)
    !reset |-> !(f_full && f_empty)
  );

  // -----------------------------------------------------------------------
  // Reset: wr_ptr, rd_ptr, counter all cleared one cycle after reset asserts
  // -----------------------------------------------------------------------
  ap_reset_wr_ptr: assert property (@(posedge clock)
    $rose(reset) |=> (wr_ptr == {AWIDTH{1'b0}})
  );

  ap_reset_rd_ptr: assert property (@(posedge clock)
    $rose(reset) |=> (rd_ptr == {AWIDTH{1'b0}})
  );

  ap_reset_counter: assert property (@(posedge clock)
    $rose(reset) |=> (counter == {AWIDTH{1'b0}})
  );

  // -----------------------------------------------------------------------
  // Write pointer increments by 1 on a valid write
  // -----------------------------------------------------------------------
  ap_wr_ptr_increment: assert property (@(posedge clock)
    (!reset && wr_en && !f_full) |=>
    (wr_ptr == ($past(wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
  );

  // -----------------------------------------------------------------------
  // Write pointer stable when no valid write
  // -----------------------------------------------------------------------
  ap_wr_ptr_stable: assert property (@(posedge clock)
    (!reset && !(wr_en && !f_full)) |=> (wr_ptr == $past(wr_ptr))
  );

  // -----------------------------------------------------------------------
  // Read pointer increments by 1 on a valid read
  // -----------------------------------------------------------------------
  ap_rd_ptr_increment: assert property (@(posedge clock)
    (!reset && rd_en && !f_empty) |=>
    (rd_ptr == ($past(rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1}))
  );

  // -----------------------------------------------------------------------
  // Read pointer stable when no valid read
  // -----------------------------------------------------------------------
  ap_rd_ptr_stable: assert property (@(posedge clock)
    (!reset && !(rd_en && !f_empty)) |=> (rd_ptr == $past(rd_ptr))
  );

  // -----------------------------------------------------------------------
  // Counter increments on write-only (no simultaneous read)
  // -----------------------------------------------------------------------
  ap_counter_increment: assert property (@(posedge clock)
    (!reset && wr_en && !f_full && !rd_en) |=>
    (counter == ($past(counter) + {{(AWIDTH-1){1'b0}}, 1'b1}))
  );

  // -----------------------------------------------------------------------
  // Counter decrements on read-only (no simultaneous write)
  // -----------------------------------------------------------------------
  ap_counter_decrement: assert property (@(posedge clock)
    (!reset && rd_en && !f_empty && !wr_en) |=>
    (counter == ($past(counter) - {{(AWIDTH-1){1'b0}}, 1'b1}))
  );

  // -----------------------------------------------------------------------
  // Counter stable on simultaneous read+write
  // -----------------------------------------------------------------------
  ap_counter_stable_rw: assert property (@(posedge clock)
    (!reset && wr_en && !f_full && rd_en && !f_empty) |=>
    (counter == $past(counter))
  );

  // -----------------------------------------------------------------------
  // Counter stable when idle
  // -----------------------------------------------------------------------
  ap_counter_stable_idle: assert property (@(posedge clock)
    (!reset && !wr_en && !rd_en) |=> (counter == $past(counter))
  );

  // -----------------------------------------------------------------------
  // No write when full: wr_ptr must not change
  // -----------------------------------------------------------------------
  ap_no_write_when_full: assert property (@(posedge clock)
    (!reset && wr_en && f_full) |=> (wr_ptr == $past(wr_ptr))
  );

  // -----------------------------------------------------------------------
  // No read when empty: rd_ptr must not change
  // -----------------------------------------------------------------------
  ap_no_read_when_empty: assert property (@(posedge clock)
    (!reset && rd_en && f_empty) |=> (rd_ptr == $past(rd_ptr))
  );

  // -----------------------------------------------------------------------
  // Counter never exceeds depth-1
  // -----------------------------------------------------------------------
  ap_counter_no_overflow: assert property (@(posedge clock)
    !reset |-> (counter <= {AWIDTH{1'b1}})
  );

  // -----------------------------------------------------------------------
  // Cover: full can be cleared by a read
  // -----------------------------------------------------------------------
  cp_full_can_clear: cover property (@(posedge clock)
    f_full ##1 (rd_en && !f_full)
  );

  // -----------------------------------------------------------------------
  // Cover: empty can be cleared by a write
  // -----------------------------------------------------------------------
  cp_empty_can_clear: cover property (@(posedge clock)
    f_empty ##1 (wr_en && !f_empty)
  );

endmodule

bind fifo fifo_sva #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) i_fifo_sva (
    .clock   (clock),
    .reset   (reset),
    .wr_en   (wr_en),
    .rd_en   (rd_en),
    .data_in (data_in),
    .f_full  (f_full),
    .f_empty (f_empty),
    .data_out(data_out),
    .wr_ptr  (wr_ptr),
    .rd_ptr  (rd_ptr),
    .counter (counter)
);
