module busyctr_assert #(
		parameter	[15:0]	MAX_AMOUNT = 22
	) (
		input wire i_clk,
		input wire i_reset,
		input wire i_start_signal,
		input reg  o_busy
	);

	reset_clears_busy: assert property (
		@(posedge i_clk) i_reset |=> !o_busy
	);

	reset_clears_counter: assert property (
		@(posedge i_clk) i_reset |=> (busyctr.counter == 0)
	);

	busy_iff_counter_nonzero: assert property (
		@(posedge i_clk) o_busy == (busyctr.counter != 0)
	);

	start_loads_counter: assert property (
		@(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter == 0)
			|=> (busyctr.counter == MAX_AMOUNT - 1)
	);

	counter_decrements: assert property (
		@(posedge i_clk) (!i_reset && busyctr.counter != 0)
			|=> (busyctr.counter == $past(busyctr.counter) - 1)
	);

	counter_stays_zero_when_idle: assert property (
		@(posedge i_clk) (!i_reset && !i_start_signal && busyctr.counter == 0)
			|=> (busyctr.counter == 0)
	);

	counter_bounded: assert property (
		@(posedge i_clk) busyctr.counter <= MAX_AMOUNT - 1
	);

	busy_deasserts_after_count: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(i_start_signal && busyctr.counter == 0)
			|-> ##MAX_AMOUNT !o_busy
	);

	no_start_when_busy_has_no_effect: assert property (
		@(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter != 0)
			|=> (busyctr.counter == $past(busyctr.counter) - 1)
	);

endmodule

bind busyctr busyctr_assert #(.MAX_AMOUNT(MAX_AMOUNT)) busyctr_assert_instance (.*);
