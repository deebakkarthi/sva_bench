module lfsr_fib_assert #(
		parameter	LN=8,
		parameter [(LN-1):0]	TAPS = 8'h2d,
				INITIAL_FILL = { { (LN-1){1'b0}}, 1'b1 }
	) (
		input	wire			i_clk, i_reset, i_ce, i_in,
		input	wire			o_bit
	);

	reset_loads_initial_fill: assert property (
		@(posedge i_clk) i_reset |=> (lfsr_fib.sreg == INITIAL_FILL)
	);

	o_bit_reflects_sreg_lsb: assert property (
		@(posedge i_clk) o_bit == lfsr_fib.sreg[0]
	);

	shift_lower_bits_on_ce: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> (lfsr_fib.sreg[(LN-2):0] == $past(lfsr_fib.sreg[(LN-1):1]))
	);

	msb_feedback_on_ce: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> (lfsr_fib.sreg[LN-1] == ($past(^(lfsr_fib.sreg & TAPS)) ^ $past(i_in)))
	);

	hold_sreg_when_no_ce: assert property (
		@(posedge i_clk) (!i_reset && !i_ce) |=> (lfsr_fib.sreg == $past(lfsr_fib.sreg))
	);

	reset_takes_priority_over_ce: assert property (
		@(posedge i_clk) (i_reset && i_ce) |=> (lfsr_fib.sreg == INITIAL_FILL)
	);

endmodule

bind lfsr_fib lfsr_fib_assert #(.LN(LN), .TAPS(TAPS), .INITIAL_FILL(INITIAL_FILL)) lfsr_fib_assert_instance (.*);
