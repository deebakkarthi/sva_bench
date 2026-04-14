module lfsr_fib_assert #(
		parameter	LN = 8,
		parameter [(LN-1):0]	TAPS = 8'h2d,
					INITIAL_FILL = { {(LN-1){1'b0}}, 1'b1 }
	) (
		input	wire	i_clk, i_reset, i_ce, i_in,
		input	wire	o_bit
	);

	// o_bit is always the LSB of the internal shift register
	o_bit_equals_sreg_lsb: assert property (
		@(posedge i_clk) o_bit === lfsr_fib.sreg[0]
	);

	// Synchronous reset loads INITIAL_FILL into sreg
	reset_loads_initial_fill: assert property (
		@(posedge i_clk) i_reset |=> lfsr_fib.sreg === INITIAL_FILL
	);

	// When CE is active and no reset, lower LN-1 bits shift right (receive upper bits)
	ce_shifts_lower_bits: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[(LN-2):0] === $past(lfsr_fib.sreg[(LN-1):1])
	);

	// When CE is active and no reset, new MSB is XOR of tapped bits and i_in
	ce_feedback_msb: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[(LN-1)] === ($past(^(lfsr_fib.sreg & TAPS)) ^ $past(i_in))
	);

	// When neither reset nor CE, sreg holds its value
	sreg_stable_without_ce_or_reset: assert property (
		@(posedge i_clk) (!i_reset && !i_ce) |=> lfsr_fib.sreg === $past(lfsr_fib.sreg)
	);

	// After reset deasserts and CE fires, lower bits must have shifted from pre-shift sreg upper
	post_reset_shift_correct: assert property (
		@(posedge i_clk) ($fell(i_reset) && i_ce) |=> lfsr_fib.sreg[(LN-2):0] === INITIAL_FILL[(LN-1):1]
	);

	// After reset deasserts and CE fires, MSB feedback is computed from INITIAL_FILL and i_in
	post_reset_msb_correct: assert property (
		@(posedge i_clk) ($fell(i_reset) && i_ce) |=> lfsr_fib.sreg[(LN-1)] === (^(INITIAL_FILL & TAPS) ^ $past(i_in))
	);

endmodule

bind lfsr_fib lfsr_fib_assert lfsr_fib_assert_instance (.*);
