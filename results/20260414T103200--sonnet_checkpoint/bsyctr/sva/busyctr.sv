module busyctr_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk, i_reset,
		input wire i_start_signal,
		input reg  o_busy
	);

	// o_busy reflects counter != 0 combinatorially
	busy_reflects_counter: assert property (
		@(posedge i_clk) o_busy == (busyctr.counter != 0)
	);

	// Reset drives counter to 0
	reset_clears_counter: assert property (
		@(posedge i_clk) i_reset |=> (busyctr.counter == 0)
	);

	// Reset drives o_busy low (via counter)
	reset_clears_busy: assert property (
		@(posedge i_clk) i_reset |=> !o_busy
	);

	// Start when idle loads MAX_AMOUNT-1
	start_loads_counter: assert property (
		@(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter == 0)
			|=> (busyctr.counter == MAX_AMOUNT - 1'b1)
	);

	// Counter decrements when busy and no reset
	counter_decrements: assert property (
		@(posedge i_clk) (!i_reset && busyctr.counter != 0)
			|=> (busyctr.counter == $past(busyctr.counter) - 1'b1)
	);

	// Counter stays 0 when idle and no start
	counter_stays_zero: assert property (
		@(posedge i_clk) (!i_reset && !i_start_signal && busyctr.counter == 0)
			|=> (busyctr.counter == 0)
	);

	// Counter never exceeds MAX_AMOUNT-1
	counter_bounded: assert property (
		@(posedge i_clk) busyctr.counter <= MAX_AMOUNT - 1'b1
	);

	// Reset takes priority over start: simultaneous reset+start clears counter
	reset_priority_over_start: assert property (
		@(posedge i_clk) (i_reset && i_start_signal) |=> (busyctr.counter == 0)
	);

	// When idle and no start, busy stays low
	idle_stays_idle: assert property (
		@(posedge i_clk) (!i_reset && !i_start_signal && !o_busy) |=> !o_busy
	);

endmodule

bind busyctr busyctr_assert busyctr_assert_instance (.*);
