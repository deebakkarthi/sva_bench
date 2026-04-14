module clkgate_assert (
	input wire i_clk, i_areset_n, i_en,
	input wire o_clk
);

output_low_at_negedge: assert property (@(negedge i_clk) !o_clk);

output_equals_latch_at_posedge: assert property (@(posedge i_clk) o_clk == clkgate.latch);

reset_clears_latch: assert property (@(posedge i_clk) !i_areset_n |-> !clkgate.latch);

reset_gates_output: assert property (@(posedge i_clk) !i_areset_n |-> !o_clk);

latch_transparent_when_clock_low: assert property (@(negedge i_clk) i_areset_n |-> (clkgate.latch == i_en));

disabled_latch_gates_output: assert property (@(posedge i_clk) !clkgate.latch |-> !o_clk);

enabled_latch_passes_clock: assert property (@(posedge i_clk) clkgate.latch |-> o_clk);

output_is_and_of_latch_and_clock: assert property (@(posedge i_clk) o_clk == (clkgate.latch & i_clk));

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
