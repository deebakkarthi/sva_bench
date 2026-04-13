`default_nettype	none
module clkgate (
		input	wire	i_clk, i_areset_n, i_en,
		output	wire	o_clk
	);

	reg	latch;

	always @(*)
	if (!i_areset_n)
		latch = 1'b0;
	else if (!i_clk)
		latch = i_en;

	assign	o_clk = (latch)&&(i_clk);
endmodule
