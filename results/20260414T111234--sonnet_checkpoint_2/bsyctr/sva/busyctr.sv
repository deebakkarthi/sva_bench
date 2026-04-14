module busyctr_assert #(
    parameter [15:0] MAX_AMOUNT = 22
) (
    input wire i_clk,
    input wire i_reset,
    input wire i_start_signal,
    input reg  o_busy
);

    reset_clears_counter: assert property (
        @(posedge i_clk) i_reset |=> (busyctr.counter == 0)
    );

    reset_deasserts_busy: assert property (
        @(posedge i_clk) i_reset |=> !o_busy
    );

    busy_reflects_counter: assert property (
        @(posedge i_clk) o_busy == (busyctr.counter != 0)
    );

    start_loads_counter: assert property (
        @(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter == 0)
        |=> (busyctr.counter == MAX_AMOUNT - 1)
    );

    counter_decrements_when_nonzero: assert property (
        @(posedge i_clk) (!i_reset && busyctr.counter != 0)
        |=> (busyctr.counter == $past(busyctr.counter) - 1'b1)
    );

    counter_stays_zero_when_idle: assert property (
        @(posedge i_clk) (!i_reset && !i_start_signal && busyctr.counter == 0)
        |=> (busyctr.counter == 0)
    );

    counter_never_exceeds_max: assert property (
        @(posedge i_clk) busyctr.counter <= MAX_AMOUNT - 1
    );

    busy_remains_high_while_counting: assert property (
        @(posedge i_clk) (!i_reset && busyctr.counter > 1) |=> o_busy
    );

    busy_deasserts_at_last_count: assert property (
        @(posedge i_clk) (!i_reset && !i_start_signal && busyctr.counter == 1)
        |=> !o_busy
    );

    busy_asserted_after_start: assert property (
        @(posedge i_clk) (!i_reset && i_start_signal && busyctr.counter == 0 && MAX_AMOUNT > 1)
        |=> o_busy
    );

endmodule

bind busyctr busyctr_assert busyctr_assert_instance (.*);
