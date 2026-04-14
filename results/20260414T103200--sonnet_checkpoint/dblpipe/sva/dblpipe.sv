module dblpipe_assert (
    input wire i_clk,
    input wire i_ce,
    input wire i_data,
    input reg  o_data
);

// Both lfsr_fib instances receive identical inputs, so their outputs must always match
lfsrs_produce_identical_outputs: assert property (
    @(posedge i_clk) dblpipe.a_data == dblpipe.b_data
);

// XOR of two identical signals is always 0, so o_data must always be 0
output_always_zero: assert property (
    @(posedge i_clk) o_data == 1'b0
);

// o_data correctly reflects the registered XOR of a_data and b_data
output_is_registered_xor: assert property (
    @(posedge i_clk) o_data == $past(dblpipe.a_data ^ dblpipe.b_data)
);

// o_data is stable when a_data and b_data are equal (no spurious transitions)
output_never_transitions_high: assert property (
    @(posedge i_clk) !o_data
);

endmodule

bind dblpipe dblpipe_assert dblpipe_assert_instance (.*);
