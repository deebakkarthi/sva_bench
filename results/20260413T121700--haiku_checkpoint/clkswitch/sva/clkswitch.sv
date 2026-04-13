```systemverilog
module clkswitch_assert (
    input wire i_clk_a,
    input wire i_clk_b,
    input wire i_areset_n,
    input wire i_sel,
    input wire o_clk
);

no_glitch: assert property (@(posedge i_clk_a or posedge i_clk_b or negedge i_areset_n)
    (i_areset_n) |-> !(clkswitch.a_sel && clkswitch.b_sel));

selectors_not_stuck: assert property (@(posedge i_clk_a or posedge i_clk_b)
    (i_areset_n && $past(i_areset_n, 10)) |-> (clkswitch.a_sel || clkswitch.b_sel));

endmodule

bind clkswitch clkswitch_assert clkswitch_assert_instance (.*);
```
