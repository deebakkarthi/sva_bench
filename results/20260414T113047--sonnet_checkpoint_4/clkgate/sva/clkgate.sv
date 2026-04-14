module clkgate_assert (
    input wire i_clk,
    input wire i_areset_n,
    input wire i_en,
    input wire o_clk
);

// When reset is active, latch must be 0
reset_clears_latch: assert property (@(posedge i_clk) !i_areset_n |-> clkgate.latch == 1'b0);

// When reset is active, output clock must be suppressed
reset_gates_output: assert property (@(posedge i_clk) !i_areset_n |-> !o_clk);

// When clock is low and not in reset, latch transparently follows i_en
latch_transparent_when_clk_low: assert property (@(negedge i_clk) i_areset_n |-> (clkgate.latch == i_en));

// Latch must hold its value during the high clock phase (no glitch propagation)
latch_stable_during_high_clock: assert property (@(posedge i_clk) i_areset_n |-> $stable(clkgate.latch));

// Output clock is always the logical AND of latch and input clock (functional correctness)
output_equals_latch_and_clk: assert property (@(posedge i_clk) o_clk == (clkgate.latch & i_clk));

// Output clock is always 0 during low clock phase (latch cannot glitch output)
output_zero_during_low_clock: assert property (@(negedge i_clk) !o_clk);

// When latch is 0 during high clock, output is suppressed
output_suppressed_when_latch_zero: assert property (@(posedge i_clk) (i_areset_n && !clkgate.latch) |-> !o_clk);

// When latch is 1 during high clock, output propagates clock
output_propagates_when_latch_set: assert property (@(posedge i_clk) (i_areset_n && clkgate.latch) |-> o_clk);

// Enable captured before rising edge must be reflected at rising edge output
enable_captured_at_negedge_drives_output: assert property (@(posedge i_clk) i_areset_n |-> (o_clk == $past(i_en, 1,, @(negedge i_clk))));

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
