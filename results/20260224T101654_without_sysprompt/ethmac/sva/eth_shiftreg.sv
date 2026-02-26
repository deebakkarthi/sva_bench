module eth_shiftreg_assert(
    input        Clk,
    input        Reset,
    input        MdcEn_n,
    input        Mdi,
    input  [4:0] Fiad,
    input  [4:0] Rgad,
    input  [15:0] CtrlData,
    input        WriteOp,
    input  [3:0] ByteSelect,
    input  [1:0] LatchByte,
    output       ShiftedBit,
    output [15:0] Prsd,
    output       LinkFail
);

    // Internal signal to observe ShiftReg
    wire [7:0] ShiftReg;
    assign ShiftReg = {ShiftedBit, 7'bx}; // Cannot directly observe; use ShiftedBit for bit[7]

    // Reset: Prsd cleared
    reset_prsd_zero : assert property (
        @(posedge Clk)
        Reset |=> (Prsd == 16'h0)
    );

    // Reset: LinkFail cleared
    reset_linkfail_zero : assert property (
        @(posedge Clk)
        Reset |=> (LinkFail == 1'b0)
    );

    // ShiftedBit is always the MSB of ShiftReg (combinational)
    // We verify by checking: after ByteSelect==4'h1 load, ShiftedBit next cycle is 1'b0 (MSB of {2'b01,...} is 0)
    shiftedbitsource_bytesel1 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h1) && !Reset) |=>
        (ShiftedBit == 1'b0)
    );

    // After ByteSelect==4'h2 load, MSB = Fiad[0]
    shiftedbitsource_bytesel2 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h2) && !Reset) |=>
        (ShiftedBit == Fiad[0])
    );

    // After ByteSelect==4'h4 load, MSB = CtrlData[15]
    shiftedbitsource_bytesel4 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h4) && !Reset) |=>
        (ShiftedBit == CtrlData[15])
    );

    // After ByteSelect==4'h8 load, MSB = CtrlData[7]
    shiftedbitsource_bytesel8 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h8) && !Reset) |=>
        (ShiftedBit == CtrlData[7])
    );

    // When no ByteSelect active, ShiftedBit (MSB of ShiftReg after shift) becomes old bit[6]
    // i.e., after shift: new ShiftReg = {ShiftReg[6:0], Mdi}, so new MSB = old ShiftReg[6]
    shift_no_byteselect : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && !Reset) |=>
        (ShiftedBit == $past(ShiftedBit, 1, MdcEn_n && (ByteSelect == 4'h0)))
        // This is tricky; simpler: after one shift ShiftedBit = what was ShiftReg[6] before
        // Let's use a more direct assertion below
    );

    // LatchByte[0]: Prsd[7:0] is updated when MdcEn_n, no ByteSelect, and LatchByte[0]
    latch_prsd_low_byte : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && LatchByte[0]) |=>
        (Prsd[7] == $past(ShiftedBit))
    );

    // LatchByte[1]: Prsd[15:8] is updated when MdcEn_n, no ByteSelect, LatchByte[1] (and not LatchByte[0])
    latch_prsd_high_byte : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && !LatchByte[0] && LatchByte[1]) |=>
        (Prsd[15] == $past(ShiftedBit))
    );

    // LinkFail updated when LatchByte[0], no ByteSelect, MdcEn_n, and Rgad==5'h01
    // LinkFail = ~ShiftReg[1] = ~old ShiftReg[1]; ShiftReg[1] is two positions below MSB
    // We can't directly observe ShiftReg[1] from ports, so assert stability when conditions not met
    linkfail_no_update_when_rgad_not_01 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && LatchByte[0] && (Rgad != 5'h01)) |=>
        $stable(LinkFail)
    );

    // LinkFail does not change when MdcEn_n is low and no reset
    linkfail_stable_when_mdcen_inactive : assert property (
        @(posedge Clk) disable iff (Reset)
        (!MdcEn_n) |=> $stable(LinkFail)
    );

    // Prsd does not change when MdcEn_n is low
    prsd_stable_when_mdcen_inactive : assert property (
        @(posedge Clk) disable iff (Reset)
        (!MdcEn_n) |=> $stable(Prsd)
    );

    // ShiftedBit stable when MdcEn_n is low (ShiftReg not updating)
    shiftedbits_stable_when_mdcen_inactive : assert property (
        @(posedge Clk) disable iff (Reset)
        (!MdcEn_n) |=> $stable(ShiftedBit)
    );

    // ByteSelect one-hot or zero: no two ByteSelect bits set simultaneously (design intent)
    byteselect_onehot_or_zero : assert property (
        @(posedge Clk) disable iff (Reset)
        MdcEn_n |-> (ByteSelect == 4'h0 || ByteSelect == 4'h1 ||
                     ByteSelect == 4'h2 || ByteSelect == 4'h4 || ByteSelect == 4'h8)
    );

    // ShiftedBit is MSB: after ByteSelect==4'h1 (value {2'b01,...}), MSB=0; verify it's 0 next cycle
    bytesel1_msb_is_zero : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && ByteSelect[0]) |=> (ShiftedBit == 1'b0)
    );

    // After ByteSelect==4'h2, next MSB = Fiad[0]
    bytesel2_msb_is_fiad0 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && ByteSelect[1] && !ByteSelect[0]) |=> (ShiftedBit == $past(Fiad[0]))
    );

    // After ByteSelect==4'h4, next MSB = CtrlData[15]
    bytesel4_msb_is_ctrldata15 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && ByteSelect[2] && !ByteSelect[1] && !ByteSelect[0]) |=>
        (ShiftedBit == $past(CtrlData[15]))
    );

    // After ByteSelect==4'h8, next MSB = CtrlData[7]
    bytesel8_msb_is_ctrldata7 : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && ByteSelect[3] && !ByteSelect[2] && !ByteSelect[1] && !ByteSelect[0]) |=>
        (ShiftedBit == $past(CtrlData[7]))
    );

    // After shift (no ByteSelect), new MSB = old ShiftReg[6]; since ShiftReg shifts left,
    // new ShiftReg[7] = old ShiftReg[6]. We cannot directly observe ShiftReg[6],
    // but we know new ShiftReg[6] = old ShiftReg[5], etc.
    // After two consecutive shifts, ShiftedBit should equal what Mdi was two cycles ago
    // Use a simpler: after shift, Prsd[7] (if LatchByte[0] fired) = old ShiftedBit
    latch_low_byte_msb_matches_old_shifted : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && LatchByte[0]) |=>
        (Prsd[7] == $past(ShiftedBit))
    );

    // Prsd[15] after LatchByte[1] = old ShiftedBit
    latch_high_byte_msb_matches_old_shifted : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && !LatchByte[0] && LatchByte[1]) |=>
        (Prsd[15] == $past(ShiftedBit))
    );

    // Prsd low byte not updated when LatchByte[0] is 0 and no reset
    prsd_low_stable_no_latch : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && !LatchByte[0]) |=> $stable(Prsd[7:0])
    );

    // Prsd high byte not updated when LatchByte[1] is 0 (or LatchByte[0] takes priority) and no reset
    prsd_high_stable_no_latch : assert property (
        @(posedge Clk) disable iff (Reset)
        (MdcEn_n && (ByteSelect == 4'h0) && !LatchByte[1]) |=> $stable(Prsd[15:8])
    );

endmodule

bind eth_shiftreg eth_shiftreg_assert eth_shiftreg_assert_instance (.*);
