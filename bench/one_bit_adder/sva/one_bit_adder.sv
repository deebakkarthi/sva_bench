module one_bit_adder_assert (
    input wire      a,
    input wire      b,
    output wire     sum,
    output wire     cy
);

    sum_xor_correctness : assert property (@(a or b) sum == (a ^ b));

    carry_and_correctness : assert property (@(a or b) cy == (a & b));

    no_carry_when_inputs_zero : assert property (@(a or b) (!a && !b) |-> (!sum && !cy));

    sum_one_carry_zero_when_one_input : assert property (@(a or b) (a ^ b) |-> (sum && !cy));

    sum_zero_carry_one_when_both_inputs_one : assert property (@(a or b) (a && b) |-> (!sum && cy));

    sum_and_carry_not_both_one : assert property (@(a or b) !(sum && cy));

    carry_implies_both_inputs_one : assert property (@(a or b) cy |-> (a && b));

    sum_high_implies_exactly_one_input : assert property (@(a or b) sum |-> (a ^ b));

endmodule

bind one_bit_adder one_bit_adder_assert one_bit_adder_assert_instance (.*);
