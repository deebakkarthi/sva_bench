`default_nettype	none
module	busyctr #(
		parameter	[15:0]	MAX_AMOUNT = 22
	) (
		input	wire	i_clk, i_reset,
		input	wire	i_start_signal,
		output	reg	o_busy
	);

	reg	[15:0]	counter;

	initial	counter = 0;
	always @(posedge i_clk)
	if (i_reset)
		counter <= 0;
	else if ((i_start_signal)&&(counter == 0))
		counter <= MAX_AMOUNT-1'b1;
	else if (counter != 0)
		counter <= counter - 1'b1;

	always @(*)
		o_busy <= (counter != 0);
endmodule
