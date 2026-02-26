module eth_clockgen_assert(
    input       Clk,
    input       Reset,
    input [7:0] Divider,
    output      Mdc,
    output      MdcEn,
    output      MdcEn_n
);

    wire [7:0] TempDivider = (Divider[7:0] < 2) ? 8'h02 : Divider[7:0];
    wire [7:0] CounterPreset = (TempDivider[7:0] >> 1) - 8'b1;
    wire [7:0] Counter;
    wire       CountEq0;

    assign CountEq0 = (Counter == 8'h0);

    // Bind internal signals via hierarchical reference
    // Use DUT's Counter
    wire [7:0] dut_counter = eth_clockgen_assert_instance.Counter;

    // Reset: Mdc must be 0 after reset
    reset_mdc_low : assert property (
        @(posedge Clk)
        Reset |=> (Mdc == 1'b0)
    );

    // Reset: Counter must be 1 after reset
    reset_counter_one : assert property (
        @(posedge Clk)
        Reset |=> ($past(Reset) ? (dut_counter == 8'h1) : 1'b1)
    );

    // TempDivider is always >= 2
    temp_divider_min_two : assert property (
        @(posedge Clk)
        TempDivider >= 8'h02
    );

    // MdcEn is combinatorial: CountEq0 & ~Mdc
    mdcen_definition : assert property (
        @(posedge Clk)
        MdcEn == (dut_counter == 8'h0 && ~Mdc)
    );

    // MdcEn_n is combinatorial: CountEq0 & Mdc
    mdcen_n_definition : assert property (
        @(posedge Clk)
        MdcEn_n == (dut_counter == 8'h0 && Mdc)
    );

    // MdcEn and MdcEn_n are mutually exclusive
    mdcen_mutual_exclusion : assert property (
        @(posedge Clk)
        !(MdcEn && MdcEn_n)
    );

    // Counter decrements by 1 when not zero and no reset
    counter_decrements : assert property (
        @(posedge Clk) disable iff (Reset)
        (dut_counter != 8'h0) |=> (dut_counter == $past(dut_counter) - 8'h1)
    );

    // Counter reloads to CounterPreset when it reaches 0
    counter_reloads : assert property (
        @(posedge Clk) disable iff (Reset)
        (dut_counter == 8'h0) |=> (dut_counter == $past(CounterPreset))
    );

    // Mdc toggles when CountEq0 (counter reaches 0)
    mdc_toggles_on_counteq0 : assert property (
        @(posedge Clk) disable iff (Reset)
        (dut_counter == 8'h0) |=> (Mdc == ~$past(Mdc))
    );

    // Mdc holds when counter not zero
    mdc_holds_when_counter_nonzero : assert property (
        @(posedge Clk) disable iff (Reset)
        (dut_counter != 8'h0) |=> (Mdc == $past(Mdc))
    );

    // MdcEn asserted only when Mdc is about to rise (Mdc currently low, counter hits 0)
    mdcen_before_mdc_rise : assert property (
        @(posedge Clk) disable iff (Reset)
        MdcEn |=> (Mdc == 1'b1)
    );

    // MdcEn_n asserted only when Mdc is about to fall (Mdc currently high, counter hits 0)
    mdcen_n_before_mdc_fall : assert property (
        @(posedge Clk) disable iff (Reset)
        MdcEn_n |=> (Mdc == 1'b0)
    );

    // Counter after reset is exactly 1
    counter_reset_value : assert property (
        @(posedge Clk)
        $rose(Reset) |=> (dut_counter == 8'h1)
    );

    // Mdc after reset is exactly 0
    mdc_reset_value : assert property (
        @(posedge Clk)
        $rose(Reset) |=> (Mdc == 1'b0)
    );

    // CounterPreset is always TempDivider/2 - 1
    counter_preset_value : assert property (
        @(posedge Clk)
        CounterPreset == (TempDivider >> 1) - 8'b1
    );

    // When divider < 2, TempDivider is clamped to 2
    temp_divider_clamp : assert property (
        @(posedge Clk)
        (Divider < 8'h02) |-> (TempDivider == 8'h02)
    );

    // When divider >= 2, TempDivider equals Divider
    temp_divider_passthrough : assert property (
        @(posedge Clk)
        (Divider >= 8'h02) |-> (TempDivider == Divider)
    );

endmodule

bind eth_clockgen eth_clockgen_assert eth_clockgen_assert_instance (.*);
