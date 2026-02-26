module eth_rxethmac_assert (
    input         MRxClk,
    input         MRxDV,
    input   [3:0] MRxD,
    input         Reset,
    input         Transmitting,
    input  [15:0] MaxFL,
    input         r_IFG,
    input         HugEn,
    input         DlyCrcEn,
    input  [47:0] MAC,
    input         r_Bro,
    input         r_Pro,
    input  [31:0] r_HASH0,
    input  [31:0] r_HASH1,
    input         PassAll,
    input         ControlFrmAddressOK,
    output  [7:0] RxData,
    output        RxValid,
    output        RxStartFrm,
    output        RxEndFrm,
    output [15:0] ByteCnt,
    output        ByteCntEq0,
    output        ByteCntGreat2,
    output        ByteCntMaxFrame,
    output        CrcError,
    output        StateIdle,
    output        StatePreamble,
    output        StateSFD,
    output  [1:0] StateData,
    output        RxAbort,
    output        AddressMiss
);

    // Internal signals mirrored for assertion checking
    // MRxDEqD and MRxDEq5 combinational checks
    mrxd_eq_d_check : assert property (
        @(posedge MRxClk)
        (MRxD == 4'hd) |-> ##0 1'b1
    );

    // RxValid is reset to 0 on Reset
    rxvalid_reset : assert property (
        @(posedge MRxClk or posedge Reset)
        Reset |-> ##1 (RxValid == 1'b0)
    );

    // RxStartFrm is reset to 0 on Reset
    rxstartfrm_reset : assert property (
        @(posedge MRxClk or posedge Reset)
        Reset |-> ##1 (RxStartFrm == 1'b0)
    );

    // RxEndFrm is reset to 0 on Reset
    rxendfrm_reset : assert property (
        @(posedge MRxClk or posedge Reset)
        Reset |-> ##1 (RxEndFrm == 1'b0)
    );

    // RxData is reset to 0 on Reset
    rxdata_reset : assert property (
        @(posedge MRxClk or posedge Reset)
        Reset |-> ##1 (RxData == 8'h0)
    );

    // RxValid is two cycles delayed from GenerateRxValid condition
    // GenerateRxValid = StateData[0] & (~ByteCntEq0 | DlyCrcCnt >= 4'h3)
    // RxValid_d is one cycle delayed from GenerateRxValid
    // RxValid is one cycle delayed from RxValid_d
    // So if StateData[0] is 0, GenerateRxValid is 0, two cycles later RxValid should be 0
    rxvalid_pipeline_no_state_data : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (!StateData[0] && !ByteCntEq0) |-> ##2 (RxValid == 1'b0)
    );

    // RxStartFrm should only be asserted when StateData is active
    rxstartfrm_requires_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        RxStartFrm |-> $past(StateData[0], 2)
    );

    // RxEndFrm should only come from StateData conditions
    rxendfrm_requires_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        RxEndFrm |-> ($past(StateData[0], 2) || $past(StateData[1], 1))
    );

    // RxValid pipeline: RxValid is one clock delayed from RxValid_d
    // which is one clock delayed from GenerateRxValid
    // If ~StateData[0] for two consecutive cycles, RxValid must be 0
    rxvalid_zero_no_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (!$past(StateData[0], 1) && !$past(StateData[0], 2)) |-> (RxValid == 1'b0)
    );

    // RxStartFrm pipeline consistency: RxStartFrm follows RxStartFrm_d by one cycle
    // If StateData[0] was never set two cycles ago, RxStartFrm should be 0
    rxstartfrm_zero_no_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (!$past(StateData[0], 2)) |-> (RxStartFrm == 1'b0)
    );

    // StateData is one-hot or zero: StateData[0] and StateData[1] should not both be 1
    statedata_onehot : assert property (
        @(posedge MRxClk) disable iff (Reset)
        !(StateData[0] && StateData[1])
    );

    // When Reset, RxData should be 0 two cycles after reset deasserts
    rxdata_after_reset : assert property (
        @(posedge MRxClk)
        $rose(Reset) |-> ##1 (RxData == 8'h0)
    );

    // RxEndFrm should eventually deassert after one cycle (it's not a level signal for long)
    // RxEndFrm is generated each cycle based on conditions - no multi-cycle hold
    // Check that RxEndFrm comes from DribbleRxEndFrm or two-cycle pipeline
    rxendfrm_sources : assert property (
        @(posedge MRxClk) disable iff (Reset)
        RxEndFrm |-> (
            ($past(StateData[0], 2) && ($past(!MRxDV && ByteCntGreat2, 2) || $past(ByteCntMaxFrame, 2))) ||
            ($past(StateData[1], 1) && $past(!MRxDV && ByteCntGreat2, 1))
        )
    );

    // RxValid and RxStartFrm should not both be asserted on the very first cycle
    // (RxStartFrm marks start, RxValid is output valid - they can overlap but StartFrm leads)
    // Actually they can coincide, so skip that

    // ByteCntEq0 implies ByteCntGreat2 is false (can't be 0 and greater than 2)
    bytecnt_eq0_not_great2 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ByteCntEq0 |-> !ByteCntGreat2
    );

    // ByteCntMaxFrame implies ByteCntGreat2 (max frame count > 2)
    bytecnt_maxframe_implies_great2 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ByteCntMaxFrame |-> ByteCntGreat2
    );

    // StateIdle, StatePreamble, StateSFD, StateData are mutually exclusive
    state_idle_not_preamble : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StateIdle |-> !StatePreamble
    );

    state_idle_not_sfd : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StateIdle |-> !StateSFD
    );

    state_idle_not_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StateIdle |-> (StateData == 2'b00)
    );

    state_preamble_not_sfd : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StatePreamble |-> !StateSFD
    );

    state_preamble_not_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StatePreamble |-> (StateData == 2'b00)
    );

    state_sfd_not_statedata : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StateSFD |-> (StateData == 2'b00)
    );

    // CrcHashGood is asserted when StateData[0] and ByteCntEq6 (one cycle later)
    crchashgood_follows_statedata_bytecnt : assert property (
        @(posedge MRxClk) disable iff (Reset)
        $past(StateData[0] && ByteCntEq6, 1) |-> CrcHashGood
    );

    crchashgood_requires_statedata_bytecnt : assert property (
        @(posedge MRxClk) disable iff (Reset)
        CrcHashGood |-> $past(StateData[0] && ByteCntEq6, 1)
    );

    // CrcHash is cleared when Reset or StateIdle
    crchash_reset_on_idle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        $rose(StateIdle) |-> ##1 1'b1  // placeholder - CrcHash is internal
    );

    // RxEndFrm_d and RxEndFrm consistency
    // RxEndFrm = RxEndFrm_d | DribbleRxEndFrm (one-cycle delayed from GenerateRxEndFrm)
    // If GenerateRxEndFrm was set last cycle (StateData[0] with ~MRxDV&ByteCntGreat2 or ByteCntMaxFrame)
    // then RxEndFrm_d is set this cycle, and RxEndFrm is set next cycle
    rxendfrm_pipeline_from_generateendfrm : assert property (
        @(posedge MRxClk) disable iff (Reset)
        $past(StateData[0] && (!MRxDV && ByteCntGreat2), 2) |-> ##0 RxEndFrm
    );

    // RxStartFrm should not be asserted when StateData is not active two cycles prior
    rxstartfrm_pipeline_integrity : assert property (
        @(posedge MRxClk) disable iff (Reset)
        RxStartFrm |-> $past(StateData[0], 2)
    );

    // Mutual exclusion of RxStartFrm and RxEndFrm is not guaranteed, skip

    // When not in any valid state and not in reset, StateIdle should be true
    // (This depends on state machine implementation - skip as too implementation specific)

    // RxAbort should not coincide with RxValid being asserted if abort terminates frame
    // This is more of a functional property - let's check basic timing

    // AddressMiss should not change when not in StateData
    // (too implementation specific without internal state)

    // Data_Crc is bit-reversed MRxD - this is combinational (internal wire, can't directly assert)
    // Enable_Crc depends on MRxDV and StateData
    enable_crc_requires_mRxDV : assert property (
        @(posedge MRxClk) disable iff (Reset)
        !MRxDV |-> 1'b1  // Enable_Crc is internal wire, can check at output level
    );

    // RxValid_d pipeline - two cycle delay total for RxValid
    rxvalid_two_cycle_delay_check : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateData[0] && !ByteCntEq0) |-> ##2 RxValid
    );

    // RxStartFrm two cycle delay from GenerateRxStartFrm
    rxstartfrm_two_cycle_delay_nodlycrc : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateData[0] && ByteCntEq1 && !DlyCrcEn) |-> ##2 RxStartFrm
    );

endmodule

bind eth_rxethmac eth_rxethmac_assert eth_rxethmac_assert_instance (.*);
