module eth_register_assert #(
    parameter WIDTH = 8,
    parameter RESET_VALUE = 0
)(
    input [WIDTH-1:0] DataIn,
    input             Write,
    input             Clk,
    input             Reset,
    input             SyncReset,
    output [WIDTH-1:0] DataOut
);

    // Async reset: DataOut must immediately become RESET_VALUE when Reset is asserted
    async_reset_assert : assert property (
        @(posedge Clk)
        Reset |-> DataOut == RESET_VALUE
    );

    // Async reset clears output regardless of clock edge
    async_reset_no_clk_assert : assert property (
        @(posedge Reset)
        DataOut == RESET_VALUE
    );

    // Sync reset: on next rising clock edge after SyncReset (without async Reset), DataOut becomes RESET_VALUE
    sync_reset_assert : assert property (
        @(posedge Clk) disable iff (Reset)
        SyncReset |=> DataOut == RESET_VALUE
    );

    // Write: when Write is asserted (no resets), DataOut captures DataIn on next clock
    write_assert : assert property (
        @(posedge Clk) disable iff (Reset)
        (!SyncReset && Write) |=> DataOut == $past(DataIn)
    );

    // No write, no reset: DataOut holds its value
    hold_assert : assert property (
        @(posedge Clk) disable iff (Reset)
        (!SyncReset && !Write) |=> DataOut == $past(DataOut)
    );

    // Sync reset takes priority over Write
    sync_reset_priority_assert : assert property (
        @(posedge Clk) disable iff (Reset)
        (SyncReset && Write) |=> DataOut == RESET_VALUE
    );

    // After async reset deasserts (without sync reset or write), DataOut holds RESET_VALUE
    post_async_reset_hold_assert : assert property (
        @(posedge Clk)
        ($fell(Reset) && !SyncReset && !Write) |=> DataOut == RESET_VALUE
    );

    // DataOut width check: DataOut must stay within WIDTH bits (always valid for reg, sanity check)
    dataout_width_assert : assert property (
        @(posedge Clk)
        DataOut == DataOut[WIDTH-1:0]
    );

endmodule

bind eth_register eth_register_assert #(
    .WIDTH(WIDTH),
    .RESET_VALUE(RESET_VALUE)
) eth_register_assert_instance (.*);
