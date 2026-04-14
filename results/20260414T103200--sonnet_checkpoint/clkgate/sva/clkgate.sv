`default_nettype none

module clkgate_assert (
		input wire i_clk, i_areset_n, i_en,
		input wire o_clk
	);

	// When reset is active, output clock must be deasserted
	reset_suppresses_output: assert property (@(posedge i_clk) !i_areset_n |-> !o_clk);

	// When reset is active, latch must be cleared
	reset_clears_latch: assert property (@(posedge i_clk) !i_areset_n |-> !clkgate.latch);

	// Output is always the AND of latch and input clock
	output_equals_latch_and_clock: assert property (@(posedge i_clk) o_clk == (clkgate.latch & i_clk));

	// Output clock can never be high when input clock is low
	output_gated_by_input_clock: assert property (@(negedge i_clk) !o_clk);

	// On negedge, latch transparently captures i_en when not in reset
	latch_captures_enable_on_negedge: assert property (@(negedge i_clk) i_areset_n |-> (clkgate.latch == i_en));

	// When latch is low at rising edge, output is suppressed
	latch_low_suppresses_output: assert property (@(posedge i_clk) !clkgate.latch |-> !o_clk);

	// When latch is high at rising edge and no reset, output follows input clock
	latch_high_passes_clock: assert property (@(posedge i_clk) (clkgate.latch && i_areset_n) |-> o_clk);

	// Gate enable: if i_en was high at last negedge and no reset, o_clk must be high at posedge
	enabled_gate_passes_posedge: assert property (@(posedge i_clk) $past(i_en, 1, , @(negedge i_clk)) && i_areset_n |-> o_clk);

	// Gate disable: if i_en was low at last negedge (and no reset), o_clk must be low at posedge
	disabled_gate_blocks_posedge: assert property (@(posedge i_clk) !$past(i_en, 1, , @(negedge i_clk)) && i_areset_n |-> !o_clk);

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
