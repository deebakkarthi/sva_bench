module reqarb_assert(
    input wire i_clk, i_reset,
    input wire i_a_req, i_a_data,
    input wire o_a_busy,
    input wire i_b_req, i_b_data,
    input wire o_b_busy,
    input wire o_req, o_data,
    input wire i_busy
);

reset_clears_owner: assert property (@(posedge i_clk) i_reset |=> !reqarb.a_is_the_owner);

only_a_req_grants_a_ownership: assert property (@(posedge i_clk) disable iff (i_reset) (i_a_req && !i_b_req) |=> reqarb.a_is_the_owner);

only_b_req_grants_b_ownership: assert property (@(posedge i_clk) disable iff (i_reset) (i_b_req && !i_a_req) |=> !reqarb.a_is_the_owner);

owner_stable_when_both_request: assert property (@(posedge i_clk) disable iff (i_reset) (i_a_req && i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner)));

owner_stable_when_no_request: assert property (@(posedge i_clk) disable iff (i_reset) (!i_a_req && !i_b_req) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner)));

o_a_busy_reflects_ownership_and_downstream: assert property (@(posedge i_clk) o_a_busy == (!reqarb.a_is_the_owner || i_busy));

o_b_busy_reflects_ownership_and_downstream: assert property (@(posedge i_clk) o_b_busy == (reqarb.a_is_the_owner || i_busy));

mutual_exclusion_not_both_free: assert property (@(posedge i_clk) !(!o_a_busy && !o_b_busy));

at_least_one_always_busy: assert property (@(posedge i_clk) o_a_busy || o_b_busy);

a_not_busy_implies_a_is_owner: assert property (@(posedge i_clk) !o_a_busy |-> reqarb.a_is_the_owner);

b_not_busy_implies_b_is_owner: assert property (@(posedge i_clk) !o_b_busy |-> !reqarb.a_is_the_owner);

o_req_mux_selects_a_when_owner: assert property (@(posedge i_clk) reqarb.a_is_the_owner |-> (o_req == i_a_req));

o_req_mux_selects_b_when_owner: assert property (@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_req == i_b_req));

o_data_mux_selects_a_when_owner: assert property (@(posedge i_clk) reqarb.a_is_the_owner |-> (o_data == i_a_data));

o_data_mux_selects_b_when_owner: assert property (@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_data == i_b_data));

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
