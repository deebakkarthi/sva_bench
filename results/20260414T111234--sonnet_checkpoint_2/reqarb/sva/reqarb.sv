module reqarb_assert (
	input wire i_clk, i_reset,
	input wire i_a_req, i_a_data,
	input wire o_a_busy,
	input wire i_b_req, i_b_data,
	input wire o_b_busy,
	input wire o_req, o_data,
	input wire i_busy
);

// Reset clears ownership
reset_clears_owner: assert property (
	@(posedge i_clk) i_reset |=> !reqarb.a_is_the_owner
);

// A exclusively requesting grants ownership to A
a_only_req_grants_a: assert property (
	@(posedge i_clk) (!i_reset && i_a_req && !i_b_req) |=> reqarb.a_is_the_owner
);

// B exclusively requesting grants ownership to B
b_only_req_grants_b: assert property (
	@(posedge i_clk) (!i_reset && i_b_req && !i_a_req) |=> !reqarb.a_is_the_owner
);

// Both requesting: ownership unchanged
both_req_ownership_stable: assert property (
	@(posedge i_clk) (!i_reset && i_a_req && i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner))
);

// Neither requesting: ownership unchanged
neither_req_ownership_stable: assert property (
	@(posedge i_clk) (!i_reset && !i_a_req && !i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner))
);

// o_a_busy correctness
a_busy_when_not_owner: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> o_a_busy
);

a_busy_when_downstream_busy: assert property (
	@(posedge i_clk) i_busy |-> o_a_busy
);

a_not_busy_when_owner_and_not_downstream_busy: assert property (
	@(posedge i_clk) (reqarb.a_is_the_owner && !i_busy) |-> !o_a_busy
);

// o_b_busy correctness
b_busy_when_owner_is_a: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> o_b_busy
);

b_busy_when_downstream_busy: assert property (
	@(posedge i_clk) i_busy |-> o_b_busy
);

b_not_busy_when_not_owner_and_not_downstream_busy: assert property (
	@(posedge i_clk) (!reqarb.a_is_the_owner && !i_busy) |-> !o_b_busy
);

// Mutual exclusivity: A and B cannot both be not-busy simultaneously
not_both_unbusy: assert property (
	@(posedge i_clk) !(!o_a_busy && !o_b_busy)
);

// o_req mux correctness
o_req_from_a_when_owner: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> (o_req == i_a_req)
);

o_req_from_b_when_not_owner: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_req == i_b_req)
);

// o_data mux correctness
o_data_from_a_when_owner: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> (o_data == i_a_data)
);

o_data_from_b_when_not_owner: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_data == i_b_data)
);

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
