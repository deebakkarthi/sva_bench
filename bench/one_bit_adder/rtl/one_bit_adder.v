module one_bit_adder (
    input wire      a,
    input wire      b,
    output wire     sum,
    output wire     cy 
    );

    assign sum = a ^ b;
    assign  cy = a & b;

endmodule
