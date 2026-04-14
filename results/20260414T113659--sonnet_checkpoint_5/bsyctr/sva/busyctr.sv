module busyctr_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk, i_reset,
		input wire i_start_signal,
		input reg  o_busy
	);

	reset_clears_counter: assert property (
		@(posedge i_clk) i_reset |=> (busyctr.counter == 0)
	);

	reset_clears_busy: assert property (
		@(posedge i_clk) i_reset |=> !o_busy
	);

	busy_reflects_counter: assert property (
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

	counter_stays_zero: assert property (
		@(posedge i_clk) (!i_reset && busyctr.counter == 0 && !i_start_signal)
			|=> (busyctr.counter == 0)
	);

	counter_never_exceeds_max: assert property (
		@(posedge i_clk) (busyctr.counter <= MAX_AMOUNT - 1)
	);

	busy_after_start: assert property (
		@(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter == 0)
			|=> o_busy
	);

	counter_reaches_zero_from_one: assert property (
		@(posedge i_clk) (!i_reset && busyctr.counter == 1)
			|=> (busyctr.counter == 0)
	);

	not_busy_when_counter_zero: assert property (
		@(posedge i_clk) (busyctr.counter == 0) |-> !o_busy
	);

	busy_when_counter_nonzero: assert property (
		@(posedge i_clk) (busyctr.counter != 0) |-> o_busy
	);

endmodule

bind busyctr busyctr_assert busyctr_assert_instance (.*);
