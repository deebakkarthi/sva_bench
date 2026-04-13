module counter_assert #(
    parameter [15:0] MAX_AMOUNT = 22
) (
    input wire i_clk,
    input wire i_start_signal,
    input wire o_busy,
    input wire [15:0] counter
);

start_loads_counter: assert property (@(posedge i_clk) (i_start_signal && counter == 0) |-> ##1 (counter == MAX_AMOUNT - 1));

counter_decrements_when_active: assert property (@(posedge i_clk) (counter > 0) |-> ##1 (counter == $past(counter) - 1));

counter_stays_at_zero: assert property (@(posedge i_clk) (counter == 0 && !i_start_signal) |-> ##1 (counter == 0));

o_busy_reflects_counter: assert property (@(posedge i_clk) o_busy == (counter != 0));

counter_bounded_max: assert property (@(posedge i_clk) counter <= MAX_AMOUNT - 1);

counter_non_negative: assert property (@(posedge i_clk) counter >= 0);

endmodule

bind counter counter_assert counter_assert_instance (.*);
