module clkgate_assert (
    input wire i_clk,
    input wire i_areset_n,
    input wire i_en,
    input wire o_clk
);

  reset_clears_latch: assert property (!i_areset_n |-> clkgate.latch == 1'b0);
  reset_disables_output: assert property (!i_areset_n |-> o_clk == 1'b0);
  latch_samples_enable: assert property (i_clk == 1'b0 && i_areset_n == 1'b1 |-> clkgate.latch == i_en);
  output_equation: assert property (o_clk == (clkgate.latch && i_clk));
  output_disabled_on_low_latch: assert property (clkgate.latch == 1'b0 |-> o_clk == 1'b0);
  output_disabled_on_low_clock: assert property (i_clk == 1'b0 |-> o_clk == 1'b0);
  output_enabled_on_both_high: assert property ((clkgate.latch == 1'b1 && i_clk == 1'b1) |-> o_clk == 1'b1);
  output_rises_safely: assert property (@(posedge o_clk) clkgate.latch == 1'b1 && i_clk == 1'b1);

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
