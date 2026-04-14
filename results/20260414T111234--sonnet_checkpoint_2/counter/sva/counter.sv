module counter_assert #(
		parameter [15:0] MAX_AMOUNT = 22
	) (
		input wire i_clk,
		input wire i_start_signal,
		input wire o_busy
	);

	// o_busy reflects counter != 0
	busy_reflects_counter: assert property (
		@(posedge i_clk) o_busy == (counter_assert_instance.counter.counter != 0)
	);

	// When start signal and counter is 0, next cycle counter == MAX_AMOUNT-1
	start_loads_counter: assert property (
		@(posedge i_clk) (i_start_signal && (counter.counter == 0)) |=>
			(counter.counter == MAX_AMOUNT - 1'b1)
	);

	// When counter is nonzero, it decrements each cycle
	counter_decrements: assert property (
		@(posedge i_clk) (counter.counter != 0) |=>
			(counter.counter == $past(counter.counter) - 1'b1)
	);

	// When counter is 0 and no start signal, counter stays 0
	counter_stays_zero: assert property (
		@(posedge i_clk) (!i_start_signal && (counter.counter == 0)) |=>
			(counter.counter == 0)
	);

	// counter never exceeds MAX_AMOUNT-1
	counter_bounded: assert property (
		@(posedge i_clk) counter.counter <= MAX_AMOUNT - 1'b1
	);

	// start signal causes busy to assert next cycle (when counter was 0)
	start_causes_busy: assert property (
		@(posedge i_clk) (i_start_signal && !o_busy) |=> o_busy
	);

	// when counter is 1, busy deasserts next cycle (assuming no start overlap)
	counter_one_then_done: assert property (
		@(posedge i_clk) (counter.counter == 1) |=> !o_busy
	);

endmodule

bind counter counter_assert #(.MAX_AMOUNT(MAX_AMOUNT)) counter_assert_instance (.*);
