module counter_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk,
		input wire i_start_signal,
		input reg  o_busy
	);

	o_busy_reflects_counter: assert property (
		@(posedge i_clk) o_busy == (counter.counter != 0));

	counter_load_on_start: assert property (
		@(posedge i_clk) (i_start_signal && counter.counter == 0) |=> (counter.counter == MAX_AMOUNT - 1'b1));

	counter_decrements_when_nonzero: assert property (
		@(posedge i_clk) (counter.counter != 0) |=> (counter.counter == $past(counter.counter) - 1'b1));

	counter_stays_zero_when_idle: assert property (
		@(posedge i_clk) (!i_start_signal && counter.counter == 0) |=> (counter.counter == 0));

	counter_max_bound: assert property (
		@(posedge i_clk) counter.counter <= MAX_AMOUNT - 1'b1);

	busy_asserted_after_start: assert property (
		@(posedge i_clk) (i_start_signal && !o_busy) |=> o_busy);

	busy_clears_after_countdown: assert property (
		@(posedge i_clk) (counter.counter == 1) |=> !o_busy);

	counter_nonzero_implies_busy: assert property (
		@(posedge i_clk) (counter.counter != 0) |-> o_busy);

	busy_implies_counter_nonzero: assert property (
		@(posedge i_clk) o_busy |-> (counter.counter != 0));

endmodule

bind counter counter_assert #(.MAX_AMOUNT(MAX_AMOUNT)) counter_assert_instance (.*);
