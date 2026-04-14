module lfsr_fib_assert #(
		parameter	LN = 8,
		parameter [(LN-1):0]	TAPS = 8'h2d,
		parameter [(LN-1):0]	INITIAL_FILL = { {(LN-1){1'b0}}, 1'b1 }
	) (
		input	wire	i_clk, i_reset, i_ce, i_in,
		input	wire	o_bit
	);

	o_bit_equals_sreg_lsb: assert property (
		@(posedge i_clk) o_bit == lfsr_fib.sreg[0]
	);

	reset_loads_initial_fill: assert property (
		@(posedge i_clk) i_reset |=> lfsr_fib.sreg == INITIAL_FILL
	);

	ce_shifts_lower_bits_right: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[(LN-2):0] == $past(lfsr_fib.sreg[(LN-1):1])
	);

	ce_updates_msb_with_feedback: assert property (
		@(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[LN-1] == ((^($past(lfsr_fib.sreg) & TAPS)) ^ $past(i_in))
	);

	no_ce_no_reset_sreg_stable: assert property (
		@(posedge i_clk) (!i_reset && !i_ce) |=> lfsr_fib.sreg == $past(lfsr_fib.sreg)
	);

	reset_overrides_ce: assert property (
		@(posedge i_clk) (i_reset && i_ce) |=> lfsr_fib.sreg == INITIAL_FILL
	);

endmodule

bind lfsr_fib lfsr_fib_assert lfsr_fib_assert_instance (.*);
