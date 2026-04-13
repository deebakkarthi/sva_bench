`default_nettype	none
module clkswitch (
		input	wire	i_clk_a, i_clk_b,
		input	wire	i_areset_n,
		input	wire	i_sel,
		output	wire	o_clk
	);

	reg		aff, bff, a_sel, b_sel;

	initial aff = 0;
	always @(posedge i_clk_a, negedge i_areset_n)
	if (!i_areset_n)
		aff = 1;
	else
		aff <= (i_sel)&&(!b_sel);

	initial a_sel = 0;
	always @(negedge i_clk_a, negedge i_areset_n)
	if (!i_areset_n)
		a_sel = 1;
	else
		a_sel <= aff;

	initial bff = 0;
	always @(posedge i_clk_b, negedge i_areset_n)
	if (!i_areset_n)
		bff <= 0;
	else
		bff <= (!i_sel)&&(!a_sel);

	initial b_sel = 0;
	always @(negedge i_clk_b, negedge i_areset_n)
	if (!i_areset_n)
		b_sel <= 0;
	else
		b_sel <= bff;

	assign	o_clk = ((a_sel)&&(i_clk_a))
			||((b_sel)&&(i_clk_b));
endmodule
