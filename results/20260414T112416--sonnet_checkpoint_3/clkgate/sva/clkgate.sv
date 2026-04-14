module clkgate_assert (
    input wire i_clk,
    input wire i_areset_n,
    input wire i_en,
    input wire o_clk
);

latch_transparent_on_low_clock: assert property (@(negedge i_clk) i_areset_n |-> (clkgate.latch == i_en));
latch_cleared_by_reset: assert property (@(negedge i_clk) !i_areset_n |-> !clkgate.latch);
output_low_when_input_clock_low: assert property (@(negedge i_clk) !o_clk);
output_equals_latch_at_rising_edge: assert property (@(posedge i_clk) o_clk == clkgate.latch);
reset_suppresses_gated_clock: assert property (@(posedge i_clk) !i_areset_n |-> !o_clk);
latch_enables_gated_clock: assert property (@(posedge i_clk) i_areset_n && clkgate.latch |-> o_clk);
latch_disables_gated_clock: assert property (@(posedge i_clk) !clkgate.latch |-> !o_clk);

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
