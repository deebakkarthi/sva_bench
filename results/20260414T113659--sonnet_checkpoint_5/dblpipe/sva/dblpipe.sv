module dblpipe_assert (
		input	wire	i_clk, i_ce,
		input	wire	i_data,
		input	reg	o_data
	);

	identical_lfsr_outputs: assert property (
		@(posedge i_clk) dblpipe.a_data == dblpipe.b_data
	);

	output_always_zero: assert property (
		@(posedge i_clk) o_data == 1'b0
	);

	output_is_xor_of_lfsr_outputs: assert property (
		@(posedge i_clk) o_data == (dblpipe.a_data ^ dblpipe.b_data)
	);

endmodule

bind dblpipe dblpipe_assert dblpipe_assert_instance (.*);
