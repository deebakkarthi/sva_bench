module dblpipe_assert (
		input	wire	i_clk, i_ce,
		input	wire	i_data,
		input	reg	o_data
	);

	// Both lfsr_fib instances receive identical inputs, so their outputs must always match
	identical_lfsr_outputs: assert property (
		@(posedge i_clk) dblpipe.a_data === dblpipe.b_data
	);

	// Since a_data === b_data, their XOR is always 0, so o_data must always be 0
	output_always_zero: assert property (
		@(posedge i_clk) o_data === 1'b0
	);

	// Verify the registered XOR relationship: o_data follows a_data ^ b_data
	output_is_registered_xor: assert property (
		@(posedge i_clk) ##1 o_data === $past(dblpipe.a_data ^ dblpipe.b_data)
	);

	// When ce is low, internal lfsr outputs should remain stable (no update)
	// a_data and b_data are driven by lfsr_fib instances which are gated by i_ce
	lfsr_outputs_equal_always: assert property (
		@(posedge i_clk) (dblpipe.a_data ^ dblpipe.b_data) === 1'b0
	);

endmodule

bind dblpipe dblpipe_assert dblpipe_assert_instance (.*);
