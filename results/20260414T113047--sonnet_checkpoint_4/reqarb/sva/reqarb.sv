module reqarb_assert (
    input wire i_clk, i_reset,
    input wire i_a_req, i_a_data,
    input wire o_a_busy,
    input wire i_b_req, i_b_data,
    input wire o_b_busy,
    input wire o_req, o_data,
    input wire i_busy
);

reset_clears_ownership:
    assert property (@(posedge i_clk) i_reset |=> !reqarb.a_is_the_owner);

only_a_req_grants_ownership_to_a:
    assert property (@(posedge i_clk) (i_a_req && !i_b_req && !i_reset) |=> reqarb.a_is_the_owner);

only_b_req_grants_ownership_to_b:
    assert property (@(posedge i_clk) (i_b_req && !i_a_req && !i_reset) |=> !reqarb.a_is_the_owner);

both_or_neither_req_ownership_unchanged:
    assert property (@(posedge i_clk) ((i_a_req == i_b_req) && !i_reset) |=> (reqarb.a_is_the_owner == $past(reqarb.a_is_the_owner)));

o_a_busy_reflects_owner_and_downstream:
    assert property (@(posedge i_clk) o_a_busy == (!reqarb.a_is_the_owner || i_busy));

o_b_busy_reflects_owner_and_downstream:
    assert property (@(posedge i_clk) o_b_busy == (reqarb.a_is_the_owner || i_busy));

downstream_busy_stalls_both_requestors:
    assert property (@(posedge i_clk) i_busy |-> (o_a_busy && o_b_busy));

downstream_free_busy_signals_are_complementary:
    assert property (@(posedge i_clk) !i_busy |-> (o_a_busy ^ o_b_busy));

downstream_free_exactly_one_requestor_can_proceed:
    assert property (@(posedge i_clk) !i_busy |-> (!o_a_busy || !o_b_busy));

o_req_muxed_from_a_when_owner:
    assert property (@(posedge i_clk) reqarb.a_is_the_owner |-> (o_req == i_a_req));

o_req_muxed_from_b_when_owner:
    assert property (@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_req == i_b_req));

o_data_muxed_from_a_when_owner:
    assert property (@(posedge i_clk) reqarb.a_is_the_owner |-> (o_data == i_a_data));

o_data_muxed_from_b_when_owner:
    assert property (@(posedge i_clk) !reqarb.a_is_the_owner |-> (o_data == i_b_data));

a_not_busy_when_owner_and_downstream_free:
    assert property (@(posedge i_clk) (reqarb.a_is_the_owner && !i_busy) |-> !o_a_busy);

b_not_busy_when_owner_and_downstream_free:
    assert property (@(posedge i_clk) (!reqarb.a_is_the_owner && !i_busy) |-> !o_b_busy);

a_busy_when_not_owner:
    assert property (@(posedge i_clk) !reqarb.a_is_the_owner |-> o_a_busy);

b_busy_when_not_owner:
    assert property (@(posedge i_clk) reqarb.a_is_the_owner |-> o_b_busy);

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
