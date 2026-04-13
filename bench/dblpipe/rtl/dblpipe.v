`default_nettype	none
module dblpipe (
		input	wire	i_clk, i_ce,
		input	wire	i_data,
		output	reg	o_data
	);

	wire	a_data, b_data;

	lfsr_fib	one(i_clk, 1'b0, i_ce, i_data, a_data);
	lfsr_fib	two(i_clk, 1'b0, i_ce, i_data, b_data);

	initial	o_data = 1'b0;
	always @(posedge i_clk)
		o_data <= a_data ^ b_data;
endmodule
