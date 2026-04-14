module reqarb_assert (
	input wire i_clk, i_reset,
	input wire i_a_req, i_a_data,
	input wire o_a_busy,
	input wire i_b_req, i_b_data,
	input wire o_b_busy,
	input wire o_req, o_data,
	input wire i_busy
);

// Reset drives a_is_the_owner to 0
reset_clears_owner: assert property (
	@(posedge i_clk) i_reset |=> (reqarb.a_is_the_owner == 1'b0)
);

// Only A requests: A becomes owner next cycle
only_a_req_grants_a: assert property (
	@(posedge i_clk) disable iff (i_reset)
	(i_a_req && !i_b_req) |=> (reqarb.a_is_the_owner == 1'b1)
);

// Only B requests: B becomes owner next cycle
only_b_req_grants_b: assert property (
	@(posedge i_clk) disable iff (i_reset)
	(i_b_req && !i_a_req) |=> (reqarb.a_is_the_owner == 1'b0)
);

// Both request: ownership unchanged
both_req_ownership_stable: assert property (
	@(posedge i_clk) disable iff (i_reset)
	(i_a_req && i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner))
);

// Neither requests: ownership unchanged
neither_req_ownership_stable: assert property (
	@(posedge i_clk) disable iff (i_reset)
	(!i_a_req && !i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner))
);

// o_a_busy correctness
o_a_busy_correct: assert property (
	@(posedge i_clk)
	o_a_busy == (!reqarb.a_is_the_owner || i_busy)
);

// o_b_busy correctness
o_b_busy_correct: assert property (
	@(posedge i_clk)
	o_b_busy == (reqarb.a_is_the_owner || i_busy)
);

// o_req correctness: follows owner's request
o_req_follows_owner: assert property (
	@(posedge i_clk)
	o_req == (reqarb.a_is_the_owner ? i_a_req : i_b_req)
);

// o_data correctness: follows owner's data
o_data_follows_owner: assert property (
	@(posedge i_clk)
	o_data == (reqarb.a_is_the_owner ? i_a_data : i_b_data)
);

// At most one requestor can be not-busy when downstream is free
mutual_exclusion_when_free: assert property (
	@(posedge i_clk)
	!i_busy |-> (!o_a_busy || !o_b_busy)
);

// When downstream is free, exactly one side is not busy
exactly_one_not_busy_when_free: assert property (
	@(posedge i_clk)
	!i_busy |-> (o_a_busy ^ o_b_busy)
);

// When downstream is busy, both sides are busy
both_busy_when_downstream_busy: assert property (
	@(posedge i_clk)
	i_busy |-> (o_a_busy && o_b_busy)
);

// A owner implies B is always busy
a_owner_implies_b_busy: assert property (
	@(posedge i_clk)
	reqarb.a_is_the_owner |-> o_b_busy
);

// B owner (not A) implies A is always busy
b_owner_implies_a_busy: assert property (
	@(posedge i_clk)
	!reqarb.a_is_the_owner |-> o_a_busy
);

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
