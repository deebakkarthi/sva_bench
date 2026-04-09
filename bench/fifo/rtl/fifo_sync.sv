// vim: set syntax=systemverilog:
`default_nettype none
module fifo_sync #(
    parameter int NUM_ELEM = 8,
    parameter int DWIDTH   = 16
) (
    input wire i_clk,
    input wire i_rst_n,
    input wire i_wr_en,
    input wire i_rd_en,
    input wire [DWIDTH-1:0] i_data,
    output reg [DWIDTH-1:0] o_data,
    output reg o_full,
    output reg o_empty
);

  reg [NUM_ELEM-1:0] fifo;
  reg [$clog2(NUM_ELEM)-1:0] wr_ptr = 0;
  reg [$clog2(NUM_ELEM)-1:0] rd_ptr = 0;
  reg [$clog2(NUM_ELEM)-1:0] count = 0;

  always @(posedge i_clk) begin

    if (!i_rst_n) begin
      {wr_ptr, rd_ptr} <= 0;
      count = 0;
    end else begin
      if (i_wr_en && !i_rd_en) begin
        if (!o_full) begin
          fifo[wr_ptr] <= i_data;
          wr_ptr <= wr_ptr + 1;
          count <= count + 1;
        end
      end else if (i_rd_en && !i_wr_en) begin
        if (!o_empty) begin
          o_data <= fifo[rd_ptr];
          rd_ptr <= rd_ptr + 1;
          count  <= count - 1;
        end
      end
    end

  end
  assign o_full  = (count == NUM_ELEM - 1);
  assign o_empty = (count == 0);
endmodule
