module eth_outputcontrol_assert(
    input         Clk,
    input         Reset,
    input         WriteOp,
    input         NoPre,
    input         InProgress,
    input         ShiftedBit,
    input   [6:0] BitCounter,
    input         MdcEn_n,
    output        Mdo,
    output        MdoEn
);

    wire SerialEn_w;
    assign SerialEn_w = (WriteOp & InProgress & (BitCounter > 7'd31 | ((BitCounter == 7'd0) & NoPre)))
                      | (~WriteOp & InProgress & ((BitCounter > 7'd31 & BitCounter < 7'd46) | ((BitCounter == 7'd0) & NoPre)));

    wire MdoEn_stage_in;
    assign MdoEn_stage_in = SerialEn_w | (InProgress & (BitCounter < 7'd32));

    wire Mdo_2d_in;
    assign Mdo_2d_in = ~SerialEn_w & (BitCounter < 7'd32);

    // Async reset: MdoEn must be 0 whenever Reset is high
    async_reset_MdoEn_active : assert property (
        @(posedge Clk) Reset |-> MdoEn == 1'b0);

    // Async reset: Mdo must be 0 whenever Reset is high
    async_reset_Mdo_active : assert property (
        @(posedge Clk) Reset |-> Mdo == 1'b0);

    // Synchronous reset effect: MdoEn remains 0 the cycle after Reset
    sync_reset_MdoEn_clears : assert property (
        @(posedge Clk) Reset |=> MdoEn == 1'b0);

    // Synchronous reset effect: Mdo remains 0 the cycle after Reset
    sync_reset_Mdo_clears : assert property (
        @(posedge Clk) Reset |=> Mdo == 1'b0);

    // MdoEn does not change when MdcEn_n is inactive (no clock enable)
    MdoEn_stable_no_MdcEn_n : assert property (
        @(posedge Clk) disable iff (Reset)
        !MdcEn_n |-> $stable(MdoEn));

    // Mdo does not change when MdcEn_n is inactive (no clock enable)
    Mdo_stable_no_MdcEn_n : assert property (
        @(posedge Clk) disable iff (Reset)
        !MdcEn_n |-> $stable(Mdo));

    // MdoEn three-stage pipeline: after 3 consecutive MdcEn_n pulses, output reflects input from 2 cycles back
    MdoEn_pipeline_depth_3 : assert property (
        @(posedge Clk) disable iff (Reset)
        MdcEn_n [*3] |-> MdoEn == $past(MdoEn_stage_in, 2));

    // SerialEn is deasserted when InProgress is deasserted
    SerialEn_zero_when_not_inprogress : assert property (
        @(posedge Clk) !InProgress |-> !SerialEn_w);

    // SerialEn is asserted during write operation when BitCounter exceeds 31
    SerialEn_write_op_high_counter : assert property (
        @(posedge Clk) (WriteOp && InProgress && BitCounter > 7'd31) |-> SerialEn_w);

    // SerialEn is asserted during read operation when BitCounter is between 32 and 45 inclusive
    SerialEn_read_op_counter_range : assert property (
        @(posedge Clk) (~WriteOp && InProgress && BitCounter > 7'd31 && BitCounter < 7'd46) |-> SerialEn_w);

    // SerialEn is asserted at BitCounter==0 when NoPre is set and InProgress
    SerialEn_nopre_zero_count : assert property (
        @(posedge Clk) (InProgress && NoPre && BitCounter == 7'd0) |-> SerialEn_w);

    // SerialEn not asserted for read op when BitCounter is 46 or above
    SerialEn_read_op_above_45_clear : assert property (
        @(posedge Clk) (~WriteOp && InProgress && BitCounter >= 7'd46 && BitCounter != 7'd0) |-> !SerialEn_w);

    // SerialEn not asserted for read op when BitCounter is 0 and NoPre is deasserted
    SerialEn_read_op_zero_no_nopre : assert property (
        @(posedge Clk) (~WriteOp && InProgress && BitCounter == 7'd0 && !NoPre) |-> !SerialEn_w);

    // MdoEn_stage_in is asserted whenever SerialEn is active
    MdoEn_stage_in_high_when_serial_en : assert property (
        @(posedge Clk) SerialEn_w |-> MdoEn_stage_in);

    // MdoEn_stage_in is asserted when InProgress and BitCounter is in preamble region
    MdoEn_stage_in_preamble_region : assert property (
        @(posedge Clk) (InProgress && BitCounter < 7'd32) |-> MdoEn_stage_in);

    // MdoEn_stage_in is deasserted when not InProgress and BitCounter >= 32
    MdoEn_stage_in_zero_inactive : assert property (
        @(posedge Clk) (!InProgress && BitCounter >= 7'd32) |-> !MdoEn_stage_in);

    // Mdo_2d_in is deasserted when SerialEn is active
    Mdo_2d_in_zero_when_serial_en : assert property (
        @(posedge Clk) SerialEn_w |-> !Mdo_2d_in);

    // Mdo_2d_in is deasserted when BitCounter is 32 or above
    Mdo_2d_in_zero_high_counter : assert property (
        @(posedge Clk) (BitCounter >= 7'd32) |-> !Mdo_2d_in);

    // Mdo_2d_in is asserted when not in SerialEn region and BitCounter < 32
    Mdo_2d_in_high_preamble_no_serial : assert property (
        @(posedge Clk) (!SerialEn_w && BitCounter < 7'd32) |-> Mdo_2d_in);

    // After 3 consecutive MdcEn_n pulses with no InProgress and high BitCounter, MdoEn must be 0
    MdoEn_zero_after_three_inactive_cycles : assert property (
        @(posedge Clk) disable iff (Reset)
        (!InProgress && BitCounter >= 7'd32 && MdcEn_n) [*3] |-> MdoEn == 1'b0);

    // MdoEn_stage_in is not asserted for write op when BitCounter <= 31 and NoPre is deasserted
    MdoEn_stage_in_excludes_write_low_counter_no_nopre : assert property (
        @(posedge Clk) (WriteOp && InProgress && BitCounter > 7'd0 && BitCounter <= 7'd31 && !NoPre)
        |-> !SerialEn_w);

endmodule

bind eth_outputcontrol eth_outputcontrol_assert eth_outputcontrol_assert_instance (.*);
