module counter_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk,
		input wire i_start_signal,
		input reg  o_busy
	);

	busy_reflects_counter: assert property (
		@(posedge i_clk) o_busy == (counter.counter != 0)
	);

	counter_loads_on_start: assert property (
		@(posedge i_clk) (i_start_signal && counter.counter == 0)
		|=> (counter.counter == MAX_AMOUNT - 1'b1)
	);

	counter_decrements_when_nonzero: assert property (
		@(posedge i_clk) (counter.counter != 0)
		|=> (counter.counter == $past(counter.counter) - 1'b1)
	);

	counter_stays_zero_when_idle: assert property (
		@(posedge i_clk) (!i_start_signal && counter.counter == 0)
		|=> (counter.counter == 0)
	);

	counter_bounded_by_max: assert property (
		@(posedge i_clk) counter.counter <= MAX_AMOUNT - 1'b1
	);

	busy_high_after_start: assert property (
		@(posedge i_clk) (i_start_signal && counter.counter == 0)
		|=> o_busy
	);

	busy_low_when_counter_zero: assert property (
		@(posedge i_clk) (counter.counter == 0) |-> !o_busy
	);

	no_reload_while_busy: assert property (
		@(posedge i_clk) (counter.counter != 0)
		|=> (counter.counter != MAX_AMOUNT - 1'b1 || $past(counter.counter) == 1)
	);

endmodule

bind counter counter_assert #(.MAX_AMOUNT(MAX_AMOUNT)) counter_assert_instance (.*);
