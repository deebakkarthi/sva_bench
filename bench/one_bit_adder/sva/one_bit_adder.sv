module one_bit_adder_assert (
    input wire      a,
    input wire      b,
    output wire     sum,
    output wire     cy
);

    sum_correct : assert property (sum == (a ^ b));
    carry_correct : assert property (cy == (a & b));
    no_carry_when_inputs_differ : assert property ((a ^ b) |-> !cy);
    carry_only_when_both_inputs_high : assert property (cy |-> (a & b));
    sum_zero_when_inputs_equal : assert property ((a == b) |-> !sum);
    sum_one_when_inputs_differ : assert property ((a ^ b) |-> sum);
    both_zero_no_sum_no_carry : assert property ((!a && !b) |-> (!sum && !cy));
    both_one_no_sum_with_carry : assert property ((a && b) |-> (!sum && cy));
    a_one_b_zero_sum_no_carry : assert property ((a && !b) |-> (sum && !cy));
    a_zero_b_one_sum_no_carry : assert property ((!a && b) |-> (sum && !cy));
    sum_and_carry_mutually_exclusive : assert property (!(sum && cy));

endmodule

bind one_bit_adder one_bit_adder_assert one_bit_adder_assert_instance (.*);
