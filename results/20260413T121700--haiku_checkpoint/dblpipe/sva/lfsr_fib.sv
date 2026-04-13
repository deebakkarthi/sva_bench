`default_nettype	none

module lfsr_fib_assert #(
	parameter	LN=8,
	parameter [(LN-1):0]	TAPS = 8'h2d,
	parameter [(LN-1):0]	INITIAL_FILL = { { (LN-1){1'b0}}, 1'b1 }
) (
	input	wire			i_clk, i_reset, i_ce, i_in,
	input	wire			o_bit
);

o_bit_is_lsb: assert property (o_bit == lfsr_fib.sreg[0]);

reset_forces_initial: assert property (@(posedge i_clk) i_reset |-> ##1 lfsr_fib.sreg == INITIAL_FILL);

hold_when_disabled: assert property (@(posedge i_clk) (!i_reset && !i_ce) |-> ##1 lfsr_fib.sreg == $past(lfsr_fib.sreg));

shift_operation: assert property (@(posedge i_clk) (!i_reset && i_ce) |-> ##1 lfsr_fib.sreg[(LN-2):0] == $past(lfsr_fib.sreg[(LN-1):1]));

feedback_operation: assert property (@(posedge i_clk) (!i_reset && i_ce) |-> ##1 lfsr_fib.sreg[(LN-1)] == (^($past(lfsr_fib.sreg) & TAPS) ^ $past(i_in)));

endmodule

bind lfsr_fib lfsr_fib_assert lfsr_fib_assert_instance (.*);
