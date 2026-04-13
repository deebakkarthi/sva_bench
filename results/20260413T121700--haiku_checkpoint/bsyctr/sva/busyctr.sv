module busyctr_assert #(
		parameter	[15:0]	MAX_AMOUNT = 22
	) (
		input	wire	i_clk, i_reset,
		input	wire	i_start_signal,
		input	wire	o_busy
	);

reset_clears_counter: assert property (@(posedge i_clk) i_reset |-> ##1 (busyctr.counter == 0));

reset_clears_busy: assert property (@(posedge i_clk) i_reset |-> ##1 (o_busy == 0));

start_loads_counter: assert property (@(posedge i_clk) (i_start_signal && (busyctr.counter == 0) && !i_reset) |-> ##1 (busyctr.counter == MAX_AMOUNT - 1));

counter_decrements: assert property (@(posedge i_clk) ((busyctr.counter > 0) && !i_reset) |-> ##1 (busyctr.counter == $past(busyctr.counter) - 1));

busy_reflects_counter: assert property (o_busy == (busyctr.counter != 0));

start_ineffective_nonzero: assert property (@(posedge i_clk) (i_start_signal && (busyctr.counter > 0) && !i_reset) |-> ##1 (busyctr.counter == $past(busyctr.counter) - 1));

counter_stays_zero_no_start: assert property (@(posedge i_clk) ((busyctr.counter == 0) && !i_start_signal && !i_reset) |-> ##1 (busyctr.counter == 0));

counter_reaches_zero: assert property (@(posedge i_clk) (i_start_signal && (busyctr.counter == 0)) |-> ##(MAX_AMOUNT - 1) (busyctr.counter == 0));

endmodule

bind busyctr busyctr_assert busyctr_assert_instance (.*);
