module eth_rxcounters_assert (
    MRxClk, Reset, MRxDV, StateIdle, StateSFD, StateData, StateDrop, StatePreamble,
    MRxDEqD, DlyCrcEn, DlyCrcCnt, Transmitting, MaxFL, r_IFG, HugEn, IFGCounterEq24,
    ByteCntEq0, ByteCntEq1, ByteCntEq2, ByteCntEq3, ByteCntEq4, ByteCntEq5, ByteCntEq6,
    ByteCntEq7, ByteCntGreat2, ByteCntSmall7, ByteCntMaxFrame, ByteCntOut
);

input         MRxClk;
input         Reset;
input         MRxDV;
input         StateSFD;
input [1:0]   StateData;
input         MRxDEqD;
input         StateIdle;
input         StateDrop;
input         DlyCrcEn;
input         StatePreamble;
input         Transmitting;
input         HugEn;
input [15:0]  MaxFL;
input         r_IFG;
input         IFGCounterEq24;
input [3:0]   DlyCrcCnt;
input         ByteCntEq0;
input         ByteCntEq1;
input         ByteCntEq2;
input         ByteCntEq3;
input         ByteCntEq4;
input         ByteCntEq5;
input         ByteCntEq6;
input         ByteCntEq7;
input         ByteCntGreat2;
input         ByteCntSmall7;
input         ByteCntMaxFrame;
input [15:0]  ByteCntOut;

// -----------------------------------------------------------------------
// IFGCounter / IFGCounterEq24
// -----------------------------------------------------------------------

ifg_r_ifg_forces_eq24 : assert property (
    @(posedge MRxClk) r_IFG |-> IFGCounterEq24
);

ifg_counter_eq24_value_or_rifg : assert property (
    @(posedge MRxClk) IFGCounterEq24 |-> (r_IFG || $past(IFGCounterEq24, 1, , @(posedge MRxClk)))
);

// -----------------------------------------------------------------------
// DlyCrcCnt sequential behavior
// -----------------------------------------------------------------------

dlycrc_reset_after_reset : assert property (
    @(posedge MRxClk) $rose(Reset) |=> DlyCrcCnt == 4'h0
);

dlycrc_reset_stable_under_reset : assert property (
    @(posedge MRxClk) Reset |-> DlyCrcCnt == 4'h0
);

dlycrc_max_value : assert property (
    @(posedge MRxClk) DlyCrcCnt <= 4'h9
);

dlycrc_wrap_9_to_0 : assert property (
    @(posedge MRxClk) disable iff (Reset)
    DlyCrcCnt == 4'h9 |=> DlyCrcCnt == 4'h0
);

dlycrc_set_to_1_on_dlycrcen_sfd : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (DlyCrcEn && StateSFD && DlyCrcCnt != 4'h9) |=> DlyCrcCnt == 4'h1
);

dlycrc_increment_when_active : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (DlyCrcEn && (|DlyCrcCnt) && DlyCrcCnt != 4'h9 && !(DlyCrcEn && StateSFD)) |=>
    DlyCrcCnt == $past(DlyCrcCnt) + 4'd1
);

dlycrc_stays_0_when_inactive : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (DlyCrcCnt == 4'h0 && !(DlyCrcEn && StateSFD)) |=> DlyCrcCnt == 4'h0
);

// -----------------------------------------------------------------------
// ByteCnt comparison output mutual exclusivity
// -----------------------------------------------------------------------

bytecnt_eq0_eq1_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq1)
);

bytecnt_eq0_eq2_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq2)
);

bytecnt_eq0_eq3_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq3)
);

bytecnt_eq0_eq4_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq4)
);

bytecnt_eq0_eq5_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq5)
);

bytecnt_eq0_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq6)
);

bytecnt_eq0_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq0 && ByteCntEq7)
);

bytecnt_eq1_eq2_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq2)
);

bytecnt_eq1_eq3_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq3)
);

bytecnt_eq1_eq4_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq4)
);

bytecnt_eq1_eq5_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq5)
);

bytecnt_eq1_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq6)
);

bytecnt_eq1_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq1 && ByteCntEq7)
);

bytecnt_eq2_eq3_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq2 && ByteCntEq3)
);

bytecnt_eq2_eq4_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq2 && ByteCntEq4)
);

bytecnt_eq2_eq5_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq2 && ByteCntEq5)
);

bytecnt_eq2_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq2 && ByteCntEq6)
);

bytecnt_eq2_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq2 && ByteCntEq7)
);

bytecnt_eq3_eq4_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq3 && ByteCntEq4)
);

bytecnt_eq3_eq5_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq3 && ByteCntEq5)
);

bytecnt_eq3_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq3 && ByteCntEq6)
);

bytecnt_eq3_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq3 && ByteCntEq7)
);

bytecnt_eq4_eq5_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq4 && ByteCntEq5)
);

bytecnt_eq4_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq4 && ByteCntEq6)
);

bytecnt_eq4_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq4 && ByteCntEq7)
);

bytecnt_eq5_eq6_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq5 && ByteCntEq6)
);

bytecnt_eq5_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq5 && ByteCntEq7)
);

bytecnt_eq6_eq7_mutex : assert property (
    @(posedge MRxClk) !(ByteCntEq6 && ByteCntEq7)
);

// -----------------------------------------------------------------------
// ByteCntGreat2 consistency
// -----------------------------------------------------------------------

bytecnt_great2_not_eq0 : assert property (
    @(posedge MRxClk) ByteCntGreat2 |-> !ByteCntEq0
);

bytecnt_great2_not_eq1 : assert property (
    @(posedge MRxClk) ByteCntGreat2 |-> !ByteCntEq1
);

bytecnt_great2_not_eq2 : assert property (
    @(posedge MRxClk) ByteCntGreat2 |-> !ByteCntEq2
);

bytecnt_eq0_not_great2 : assert property (
    @(posedge MRxClk) ByteCntEq0 |-> !ByteCntGreat2
);

bytecnt_eq1_not_great2 : assert property (
    @(posedge MRxClk) ByteCntEq1 |-> !ByteCntGreat2
);

bytecnt_eq2_not_great2 : assert property (
    @(posedge MRxClk) ByteCntEq2 |-> !ByteCntGreat2
);

bytecnt_eq3_implies_great2 : assert property (
    @(posedge MRxClk) ByteCntEq3 |-> ByteCntGreat2
);

bytecnt_eq4_implies_great2 : assert property (
    @(posedge MRxClk) ByteCntEq4 |-> ByteCntGreat2
);

bytecnt_eq5_implies_great2 : assert property (
    @(posedge MRxClk) ByteCntEq5 |-> ByteCntGreat2
);

bytecnt_eq6_implies_great2 : assert property (
    @(posedge MRxClk) ByteCntEq6 |-> ByteCntGreat2
);

bytecnt_eq7_implies_great2 : assert property (
    @(posedge MRxClk) ByteCntEq7 |-> ByteCntGreat2
);

// -----------------------------------------------------------------------
// ByteCntSmall7 consistency
// -----------------------------------------------------------------------

bytecnt_eq7_not_small7 : assert property (
    @(posedge MRxClk) ByteCntEq7 |-> !ByteCntSmall7
);

bytecnt_small7_not_eq7 : assert property (
    @(posedge MRxClk) ByteCntSmall7 |-> !ByteCntEq7
);

bytecnt_eq0_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq0 |-> ByteCntSmall7
);

bytecnt_eq1_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq1 |-> ByteCntSmall7
);

bytecnt_eq2_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq2 |-> ByteCntSmall7
);

bytecnt_eq3_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq3 |-> ByteCntSmall7
);

bytecnt_eq4_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq4 |-> ByteCntSmall7
);

bytecnt_eq5_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq5 |-> ByteCntSmall7
);

bytecnt_eq6_implies_small7 : assert property (
    @(posedge MRxClk) ByteCntEq6 |-> ByteCntSmall7
);

// -----------------------------------------------------------------------
// ByteCntMaxFrame consistency
// -----------------------------------------------------------------------

bytecnt_maxframe_requires_no_hugen : assert property (
    @(posedge MRxClk) ByteCntMaxFrame |-> !HugEn
);

bytecnt_hugen_no_maxframe : assert property (
    @(posedge MRxClk) HugEn |-> !ByteCntMaxFrame
);

// -----------------------------------------------------------------------
// ByteCntOut relationship to DlyCrcEn
// -----------------------------------------------------------------------

bytecnt_out_no_dlycrc_eq0 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq0) |-> ByteCntOut == 16'd0
);

bytecnt_out_no_dlycrc_eq1 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq1) |-> ByteCntOut == 16'd1
);

bytecnt_out_no_dlycrc_eq2 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq2) |-> ByteCntOut == 16'd2
);

bytecnt_out_no_dlycrc_eq3 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq3) |-> ByteCntOut == 16'd3
);

bytecnt_out_no_dlycrc_eq4 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq4) |-> ByteCntOut == 16'd4
);

bytecnt_out_no_dlycrc_eq5 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq5) |-> ByteCntOut == 16'd5
);

bytecnt_out_no_dlycrc_eq6 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq6) |-> ByteCntOut == 16'd6
);

bytecnt_out_no_dlycrc_eq7 : assert property (
    @(posedge MRxClk) (!DlyCrcEn && ByteCntEq7) |-> ByteCntOut == 16'd7
);

bytecnt_out_dlycrc_eq0 : assert property (
    @(posedge MRxClk) (DlyCrcEn && ByteCntEq0) |-> ByteCntOut == 16'd4
);

bytecnt_out_dlycrc_eq1 : assert property (
    @(posedge MRxClk) (DlyCrcEn && ByteCntEq1) |-> ByteCntOut == 16'd5
);

bytecnt_out_dlycrc_eq2 : assert property (
    @(posedge MRxClk) (DlyCrcEn && ByteCntEq2) |-> ByteCntOut == 16'd6
);

bytecnt_out_dlycrc_eq3 : assert property (
    @(posedge MRxClk) (DlyCrcEn && ByteCntEq3) |-> ByteCntOut == 16'd7
);

bytecnt_out_dlycrc_eq4 : assert property (
    @(posedge MRxClk) (DlyCrcEn && ByteCntEq4) |-> ByteCntOut == 16'd8
);

// -----------------------------------------------------------------------
// ByteCnt after reset
// -----------------------------------------------------------------------

bytecnt_eq0_after_reset : assert property (
    @(posedge MRxClk) $rose(Reset) |=> ByteCntEq0
);

bytecnt_out_zero_after_reset_no_dlycrc : assert property (
    @(posedge MRxClk) disable iff (Reset)
    ($rose(Reset)) |=> (!DlyCrcEn |-> ByteCntOut == 16'd0)
);

endmodule

bind eth_rxcounters eth_rxcounters_assert eth_rxcounters_assert_instance (.*);
