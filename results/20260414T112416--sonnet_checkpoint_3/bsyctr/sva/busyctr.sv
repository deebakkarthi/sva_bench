module busyctr_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk, i_reset,
		input wire i_start_signal,
		input reg  o_busy
	);

	// o_busy reflects counter != 0
	busy_high_when_counter_nonzero: assert property (
		@(posedge i_clk) (busyctr.counter != 0) |-> o_busy
	);

	busy_low_when_counter_zero: assert property (
		@(posedge i_clk) (busyctr.counter == 0) |-> !o_busy
	);

	// Reset clears counter and busy
	reset_clears_busy: assert property (
		@(posedge i_clk) i_reset |=> !o_busy
	);

	reset_clears_counter: assert property (
		@(posedge i_clk) i_reset |=> (busyctr.counter == 0)
	);

	// Start signal loads MAX_AMOUNT-1 when idle
	start_loads_counter: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(i_start_signal && busyctr.counter == 0) |=> (busyctr.counter == MAX_AMOUNT - 1)
	);

	// Counter decrements when non-zero and no start
	counter_decrements: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(busyctr.counter != 0 && !(i_start_signal && busyctr.counter == 0))
		|=> (busyctr.counter == $past(busyctr.counter) - 1)
	);

	// Counter stays zero when idle and no start
	counter_stays_zero: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(busyctr.counter == 0 && !i_start_signal) |=> (busyctr.counter == 0)
	);

	// Counter never exceeds MAX_AMOUNT-1
	counter_bounded: assert property (
		@(posedge i_clk) busyctr.counter <= MAX_AMOUNT - 1
	);

	// After start, busy goes high next cycle
	start_causes_busy: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(i_start_signal && busyctr.counter == 0 && MAX_AMOUNT > 1) |=> o_busy
	);

	// Busy eventually clears after start (liveness: counter reaches 0)
	busy_clears_after_max_cycles: assert property (
		@(posedge i_clk) disable iff (i_reset)
		(i_start_signal && busyctr.counter == 0) |=>
		##[1:MAX_AMOUNT] !o_busy
	);

endmodule

bind busyctr busyctr_assert #(.MAX_AMOUNT(MAX_AMOUNT)) busyctr_assert_instance (.*);
