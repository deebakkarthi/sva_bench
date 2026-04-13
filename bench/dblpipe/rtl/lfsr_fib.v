`default_nettype	none
module	lfsr_fib #(
		parameter	LN=8,
		parameter [(LN-1):0]	TAPS = 8'h2d,
				INITIAL_FILL = { { (LN-1){1'b0}}, 1'b1 }
	) (
		input	wire			i_clk, i_reset, i_ce, i_in,
		output	wire			o_bit
	);

	reg	[(LN-1):0]	sreg;

	initial	sreg = INITIAL_FILL;
	always @(posedge i_clk)
	if (i_reset)
		sreg <= INITIAL_FILL;
	else if (i_ce)
	begin
		sreg[(LN-2):0] <= sreg[(LN-1):1];
		sreg[(LN-1)] <= (^(sreg & TAPS)) ^ i_in;
	end

	assign	o_bit = sreg[0];

endmodule
