module clkgate_assert (
    input wire i_clk,
    input wire i_areset_n,
    input wire i_en,
    input wire o_clk
);

    // Async reset immediately clears the latch
    latch_cleared_by_async_reset: assert property (
        @(negedge i_areset_n) !clkgate.latch
    );

    // Latch remains zero while reset is held, checked at each rising clock edge
    latch_zero_while_reset_held: assert property (
        @(posedge i_clk) !i_areset_n |-> !clkgate.latch
    );

    // Output is always low during the low phase of the input clock
    output_low_when_clk_low: assert property (
        @(negedge i_clk) !o_clk
    );

    // Latch is transparent when clock is low and reset is inactive
    latch_transparent_when_clk_low: assert property (
        @(negedge i_clk) i_areset_n |-> (clkgate.latch == i_en)
    );

    // Output reflects latch state at rising edge of clock (latch is opaque during high phase)
    output_equals_latch_at_rising_edge: assert property (
        @(posedge i_clk) o_clk == clkgate.latch
    );

    // Enable propagates to latch while clock is low and reset is inactive
    enable_propagates_to_latch: assert property (
        @(posedge i_en) (!i_clk && i_areset_n) |-> clkgate.latch
    );

    // Disable propagates to latch while clock is low and reset is inactive
    disable_propagates_to_latch: assert property (
        @(negedge i_en) (!i_clk && i_areset_n) |-> !clkgate.latch
    );

    // Output is never high when reset is active, checked at rising clock edge
    output_low_during_reset: assert property (
        @(posedge i_clk) !i_areset_n |-> !o_clk
    );

    // Output clock can only be high when the input clock is also high
    output_requires_input_clock: assert property (
        @(posedge i_en) !i_clk |-> !o_clk
    );

endmodule

bind clkgate clkgate_assert clkgate_assert_instance (.*);
