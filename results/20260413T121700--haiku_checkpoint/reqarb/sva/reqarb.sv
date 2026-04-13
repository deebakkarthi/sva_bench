module reqarb_assert (
	input wire i_clk, i_reset,
	input wire i_a_req, i_a_data,
	input wire o_a_busy,
	input wire i_b_req, i_b_data,
	input wire o_b_busy,
	input wire o_req, o_data,
	input wire i_busy
);

a_busy_correct_when_owner: assert property (@(posedge i_clk) disable iff (i_reset) reqarb.a_is_the_owner |-> o_a_busy == i_busy);

a_busy_correct_when_not_owner: assert property (@(posedge i_clk) disable iff (i_reset) !reqarb.a_is_the_owner |-> o_a_busy == 1'b1);

b_busy_correct_when_a_owner: assert property (@(posedge i_clk) disable iff (i_reset) reqarb.a_is_the_owner |-> o_b_busy == 1'b1);

b_busy_correct_when_b_owner: assert property (@(posedge i_clk) disable iff (i_reset) !reqarb.a_is_the_owner |-> o_b_busy == i_busy);

data_from_a_when_owner: assert property (@(posedge i_clk) disable iff (i_reset) reqarb.a_is_the_owner |-> o_data == i_a_data);

data_from_b_when_not_owner: assert property (@(posedge i_clk) disable iff (i_reset) !reqarb.a_is_the_owner |-> o_data == i_b_data);

req_from_a_when_owner: assert property (@(posedge i_clk) disable iff (i_reset) reqarb.a_is_the_owner |-> o_req == i_a_req);

req_from_b_when_not_owner: assert property (@(posedge i_clk) disable iff (i_reset) !reqarb.a_is_the_owner |-> o_req == i_b_req);

a_ownership_on_exclusive_request: assert property (@(posedge i_clk) disable iff (i_reset) (i_a_req && !i_b_req) |=> reqarb.a_is_the_owner == 1'b1);

b_ownership_on_exclusive_request: assert property (@(posedge i_clk) disable iff (i_reset) (i_b_req && !i_a_req) |=> reqarb.a_is_the_owner == 1'b0);

endmodule

bind reqarb reqarb_assert reqarb_assert_instance (.*);
