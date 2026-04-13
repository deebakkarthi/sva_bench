`default_nettype	none
module	reqarb(
	input	wire	i_clk, i_reset,
	input	wire	i_a_req, i_a_data,
	output	wire	o_a_busy,
	input	wire	i_b_req, i_b_data,
	output	wire	o_b_busy,
	output	wire	o_req, o_data,
	input	wire	i_busy
);

reg	a_is_the_owner;
initial	a_is_the_owner = 1'b0;
always @(posedge i_clk)
	if (i_reset)
		a_is_the_owner <= 1'b0;
	else if ((i_a_req)&&(!i_b_req))
		a_is_the_owner <= 1'b1;
	else if ((i_b_req)&&(!i_a_req))
		a_is_the_owner <= 1'b0;

	assign	o_a_busy = (!a_is_the_owner)||(i_busy);

	assign	o_b_busy = ( a_is_the_owner)||(i_busy);

	assign	o_req  = (a_is_the_owner) ? i_a_req  : i_b_req;
	assign	o_data = (a_is_the_owner) ? i_a_data : i_b_data;
endmodule
