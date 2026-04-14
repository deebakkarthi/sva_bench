module dblpipe_assert (
		input wire i_clk, i_ce,
		input wire i_data,
		input reg  o_data
	);

	// Both LFSR instances receive identical inputs, so their outputs must always match
	identical_outputs: assert property (
		@(posedge i_clk) dblpipe.a_data === dblpipe.b_data
	);

	// XOR of two identical signals is always zero, so o_data must always be zero
	output_always_zero: assert property (
		@(posedge i_clk) o_data === 1'b0
	);

	// o_data is registered as a_data XOR b_data
	output_is_xor_of_pipe_outputs: assert property (
		@(posedge i_clk) ##1 o_data === ($past(dblpipe.a_data) ^ $past(dblpipe.b_data))
	);

	// o_data must remain stable at zero cycle after cycle
	output_stable_zero: assert property (
		@(posedge i_clk) o_data |-> ##1 !o_data
	);

endmodule

bind dblpipe dblpipe_assert dblpipe_assert_instance (.*);
