module top(
	input CLK,
	input RST,
	input p,
	output q
);

flip flip_inst(p, q);
endmodule


module flip(input p, output not_p);
assign not_p  = ~p;
dummy d1();
dummy d2();
endmodule

module dummy();
dummy2 d1();
endmodule

module dummy2();
endmodule
