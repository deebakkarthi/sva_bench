module reqarb_assert (
	input wire i_clk, i_reset,
	input wire i_a_req, i_a_data,
	input wire o_a_busy,
	input wire i_b_req, i_b_data,
	input wire o_b_busy,
	input wire o_req, o_data,
	input wire i_busy
);

reset_clears_owner: assert property (
	@(posedge i_clk) i_reset |=> !reqarb.a_is_the_owner
);

only_a_req_grants_a_ownership: assert property (
	@(posedge i_clk) (!i_reset && i_a_req && !i_b_req) |=> reqarb.a_is_the_owner
);

only_b_req_clears_a_ownership: assert property (
	@(posedge i_clk) (!i_reset && i_b_req && !i_a_req) |=> !reqarb.a_is_the_owner
);

both_or_neither_req_ownership_stable: assert property (
	@(posedge i_clk) (!i_reset && (i_a_req == i_b_req)) |=>
		(reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner))
);

o_a_busy_when_not_owner: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> o_a_busy
);

o_a_busy_when_downstream_busy: assert property (
	@(posedge i_clk) i_busy |-> o_a_busy
);

o_a_not_busy_when_owner_and_downstream_free: assert property (
	@(posedge i_clk) (reqarb.a_is_the_owner && !i_busy) |-> !o_a_busy
);

o_b_busy_when_a_is_owner: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> o_b_busy
);

o_b_busy_when_downstream_busy: assert property (
	@(posedge i_clk) i_busy |-> o_b_busy
);

o_b_not_busy_when_b_owns_and_downstream_free: assert property (
	@(posedge i_clk) (!reqarb.a_is_the_owner && !i_busy) |-> !o_b_busy
);

mutual_exclusion_not_both_free: assert property (
	@(posedge i_clk) !(o_a_busy == 1'b0 && o_b_busy == 1'b0)
);

downstream_free_implies_exactly_one_free: assert property (
	@(posedge i_clk) !i_busy |-> (o_a_busy ^ o_b_busy)
);

o_req_follows_a_when_a_owns: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> (o_req == i_a_req)
);

o_req_follows_b_when_b_owns: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_req == i_b_req)
);

o_data_follows_a_when_a_owns: assert property (
	@(posedge i_clk) reqarb.a_is_the_owner |-> (o_data == i_a_data)
);

o_data_follows_b_when_b_owns: assert property (
	@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_data == i_b_data)
);

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
