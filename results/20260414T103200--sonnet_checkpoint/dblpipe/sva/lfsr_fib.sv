module lfsr_fib_assert #(
    parameter LN = 8,
    parameter [(LN-1):0] TAPS = 8'h2d,
    parameter [(LN-1):0] INITIAL_FILL = { {(LN-1){1'b0}}, 1'b1 }
) (
    input wire i_clk,
    input wire i_reset,
    input wire i_ce,
    input wire i_in,
    input wire o_bit
);

// o_bit is always the LSB of the shift register
output_is_sreg_lsb: assert property (
    @(posedge i_clk) o_bit == lfsr_fib.sreg[0]
);

// After reset, sreg must equal INITIAL_FILL
reset_loads_initial_fill: assert property (
    @(posedge i_clk) i_reset |=> lfsr_fib.sreg == INITIAL_FILL
);

// When ce is active and no reset, lower bits shift right (sreg[k] <- sreg[k+1])
shift_register_lower_bits: assert property (
    @(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[(LN-2):0] == $past(lfsr_fib.sreg[(LN-1):1])
);

// When ce is active and no reset, MSB gets XOR feedback of tapped bits and i_in
feedback_msb_computation: assert property (
    @(posedge i_clk) (!i_reset && i_ce) |=> lfsr_fib.sreg[(LN-1)] == ($past(^(lfsr_fib.sreg & TAPS)) ^ $past(i_in))
);

// When neither reset nor ce, sreg must hold its value
sreg_holds_when_idle: assert property (
    @(posedge i_clk) (!i_reset && !i_ce) |=> lfsr_fib.sreg == $past(lfsr_fib.sreg)
);

// sreg is never all-zeros when INITIAL_FILL is nonzero (LFSR must not lock up)
sreg_never_zero: assert property (
    @(posedge i_clk) (INITIAL_FILL != {LN{1'b0}}) |-> lfsr_fib.sreg != {LN{1'b0}}
);

endmodule

bind lfsr_fib lfsr_fib_assert #(.LN(LN), .TAPS(TAPS), .INITIAL_FILL(INITIAL_FILL)) lfsr_fib_assert_instance (.*);
