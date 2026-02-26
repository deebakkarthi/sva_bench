module eth_macstatus_assert(
    MRxClk, Reset, ReceivedLengthOK, ReceiveEnd, ReceivedPacketGood, RxCrcError,
    MRxErr, MRxDV, RxStateSFD, RxStateData, RxStatePreamble, RxStateIdle, Transmitting,
    RxByteCnt, RxByteCntEq0, RxByteCntGreat2, RxByteCntMaxFrame,
    InvalidSymbol, MRxD, LatchedCrcError, Collision, CollValid, RxLateCollision,
    r_RecSmall, r_MinFL, r_MaxFL, ShortFrame, DribbleNibble, ReceivedPacketTooBig, r_HugEn,
    LoadRxStatus, StartTxDone, StartTxAbort, RetryCnt, RetryCntLatched, MTxClk, MaxCollisionOccured,
    RetryLimit, LateCollision, LateCollLatched, DeferIndication, DeferLatched, RstDeferLatched, TxStartFrm,
    StatePreamble, StateData, CarrierSense, CarrierSenseLost, TxUsedData, LatchedMRxErr, Loopback,
    r_FullD
);

input         MRxClk;
input         Reset;
input         RxCrcError;
input         MRxErr;
input         MRxDV;
input         RxStateSFD;
input   [1:0] RxStateData;
input         RxStatePreamble;
input         RxStateIdle;
input         Transmitting;
input  [15:0] RxByteCnt;
input         RxByteCntEq0;
input         RxByteCntGreat2;
input         RxByteCntMaxFrame;
input   [3:0] MRxD;
input         Collision;
input   [5:0] CollValid;
input         r_RecSmall;
input  [15:0] r_MinFL;
input  [15:0] r_MaxFL;
input         r_HugEn;
input         StartTxDone;
input         StartTxAbort;
input   [3:0] RetryCnt;
input         MTxClk;
input         MaxCollisionOccured;
input         LateCollision;
input         DeferIndication;
input         TxStartFrm;
input         StatePreamble;
input   [1:0] StateData;
input         CarrierSense;
input         TxUsedData;
input         Loopback;
input         r_FullD;
input         ReceivedLengthOK;
input         ReceiveEnd;
input         ReceivedPacketGood;
input         InvalidSymbol;
input         LatchedCrcError;
input         RxLateCollision;
input         ShortFrame;
input         DribbleNibble;
input         ReceivedPacketTooBig;
input         LoadRxStatus;
input   [3:0] RetryCntLatched;
input         RetryLimit;
input         LateCollLatched;
input         DeferLatched;
input         RstDeferLatched;
input         CarrierSenseLost;
input         LatchedMRxErr;

// -------------------------------------------------------------------------
// LatchedCrcError assertions
// -------------------------------------------------------------------------

latched_crc_error_reset : assert property (
    @(posedge MRxClk) Reset |=> (LatchedCrcError == 1'b0)
);

latched_crc_error_clear_on_sfd : assert property (
    @(posedge MRxClk) disable iff (Reset)
    RxStateSFD |=> (LatchedCrcError == 1'b0)
);

latched_crc_error_update_on_state_data0 : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~RxStateSFD && RxStateData[0]) |=> (LatchedCrcError == ($past(RxCrcError) & ~$past(RxByteCntEq0)))
);

// -------------------------------------------------------------------------
// LatchedMRxErr assertions
// -------------------------------------------------------------------------

latched_mrx_err_reset : assert property (
    @(posedge MRxClk) Reset |=> (LatchedMRxErr == 1'b0)
);

latched_mrx_err_set_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (MRxErr && MRxDV && (RxStatePreamble || RxStateSFD || (|RxStateData) || (RxStateIdle && ~Transmitting)))
    |=> (LatchedMRxErr == 1'b1)
);

latched_mrx_err_clear_no_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~(MRxErr && MRxDV && (RxStatePreamble || RxStateSFD || (|RxStateData) || (RxStateIdle && ~Transmitting))))
    |=> (LatchedMRxErr == 1'b0)
);

// -------------------------------------------------------------------------
// ReceivedPacketGood combinational
// -------------------------------------------------------------------------

received_packet_good_combo : assert property (
    @(posedge MRxClk)
    ReceivedPacketGood == ~LatchedCrcError
);

// -------------------------------------------------------------------------
// ReceivedLengthOK combinational
// -------------------------------------------------------------------------

received_length_ok_combo : assert property (
    @(posedge MRxClk)
    ReceivedLengthOK == (RxByteCnt >= r_MinFL && RxByteCnt <= r_MaxFL)
);

// -------------------------------------------------------------------------
// LoadRxStatus assertions
// -------------------------------------------------------------------------

load_rx_status_reset : assert property (
    @(posedge MRxClk) Reset |=> (LoadRxStatus == 1'b0)
);

load_rx_status_follows_take_sample : assert property (
    @(posedge MRxClk) disable iff (Reset)
    1'b1 |=> (LoadRxStatus == $past((|RxStateData) & ~MRxDV | RxStateData[0] & MRxDV & RxByteCntMaxFrame))
);

// -------------------------------------------------------------------------
// ReceiveEnd assertions
// -------------------------------------------------------------------------

receive_end_reset : assert property (
    @(posedge MRxClk) Reset |=> (ReceiveEnd == 1'b0)
);

receive_end_follows_load_rx_status : assert property (
    @(posedge MRxClk) disable iff (Reset)
    1'b1 |=> (ReceiveEnd == $past(LoadRxStatus))
);

// -------------------------------------------------------------------------
// InvalidSymbol assertions
// -------------------------------------------------------------------------

invalid_symbol_reset : assert property (
    @(posedge MRxClk) Reset |=> (InvalidSymbol == 1'b0)
);

invalid_symbol_set : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (MRxDV && MRxErr && MRxD[3:0] == 4'he) |=> (InvalidSymbol == 1'b1)
);

invalid_symbol_clear_on_load_no_set : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (LoadRxStatus && ~(MRxDV && MRxErr && MRxD[3:0] == 4'he)) |=> (InvalidSymbol == 1'b0)
);

// -------------------------------------------------------------------------
// RxLateCollision assertions
// -------------------------------------------------------------------------

rx_late_collision_reset : assert property (
    @(posedge MRxClk) Reset |=> (RxLateCollision == 1'b0)
);

rx_late_collision_clear_on_load_rx_status : assert property (
    @(posedge MRxClk) disable iff (Reset)
    LoadRxStatus |=> (RxLateCollision == 1'b0)
);

rx_late_collision_set_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~LoadRxStatus && Collision && ~r_FullD && (~RxLateCollision || r_RecSmall))
    |=> (RxLateCollision == 1'b1)
);

// -------------------------------------------------------------------------
// ShortFrame assertions
// -------------------------------------------------------------------------

short_frame_reset : assert property (
    @(posedge MRxClk) Reset |=> (ShortFrame == 1'b0)
);

short_frame_clear_on_load_rx_status : assert property (
    @(posedge MRxClk) disable iff (Reset)
    LoadRxStatus |=> (ShortFrame == 1'b0)
);

short_frame_set_on_take_sample : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~LoadRxStatus && ((|RxStateData) & ~MRxDV | RxStateData[0] & MRxDV & RxByteCntMaxFrame))
    |=> (ShortFrame == ($past(RxByteCnt) < $past(r_MinFL)))
);

// -------------------------------------------------------------------------
// DribbleNibble assertions
// -------------------------------------------------------------------------

dribble_nibble_reset : assert property (
    @(posedge MRxClk) Reset |=> (DribbleNibble == 1'b0)
);

dribble_nibble_clear_on_sfd : assert property (
    @(posedge MRxClk) disable iff (Reset)
    RxStateSFD |=> (DribbleNibble == 1'b0)
);

dribble_nibble_set_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~RxStateSFD && ~MRxDV && RxStateData[1]) |=> (DribbleNibble == 1'b1)
);

// -------------------------------------------------------------------------
// ReceivedPacketTooBig assertions
// -------------------------------------------------------------------------

received_packet_too_big_reset : assert property (
    @(posedge MRxClk) Reset |=> (ReceivedPacketTooBig == 1'b0)
);

received_packet_too_big_clear_on_load_rx_status : assert property (
    @(posedge MRxClk) disable iff (Reset)
    LoadRxStatus |=> (ReceivedPacketTooBig == 1'b0)
);

received_packet_too_big_set_on_take_sample : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (~LoadRxStatus && ((|RxStateData) & ~MRxDV | RxStateData[0] & MRxDV & RxByteCntMaxFrame))
    |=> (ReceivedPacketTooBig == (~$past(r_HugEn) & ($past(RxByteCnt) > $past(r_MaxFL))))
);

// -------------------------------------------------------------------------
// RetryCntLatched assertions
// -------------------------------------------------------------------------

retry_cnt_latched_reset : assert property (
    @(posedge MTxClk) Reset |=> (RetryCntLatched == 4'h0)
);

retry_cnt_latched_on_start_tx : assert property (
    @(posedge MTxClk) disable iff (Reset)
    (StartTxDone || StartTxAbort) |=> (RetryCntLatched == $past(RetryCnt))
);

// -------------------------------------------------------------------------
// RetryLimit assertions
// -------------------------------------------------------------------------

retry_limit_reset : assert property (
    @(posedge MTxClk) Reset |=> (RetryLimit == 1'b0)
);

retry_limit_latched_on_start_tx : assert property (
    @(posedge MTxClk) disable iff (Reset)
    (StartTxDone || StartTxAbort) |=> (RetryLimit == $past(MaxCollisionOccured))
);

// -------------------------------------------------------------------------
// LateCollLatched assertions
// -------------------------------------------------------------------------

late_coll_latched_reset : assert property (
    @(posedge MTxClk) Reset |=> (LateCollLatched == 1'b0)
);

late_coll_latched_on_start_tx : assert property (
    @(posedge MTxClk) disable iff (Reset)
    (StartTxDone || StartTxAbort) |=> (LateCollLatched == $past(LateCollision))
);

// -------------------------------------------------------------------------
// DeferLatched assertions
// -------------------------------------------------------------------------

defer_latched_reset : assert property (
    @(posedge MTxClk) Reset |=> (DeferLatched == 1'b0)
);

defer_latched_set_on_defer_indication : assert property (
    @(posedge MTxClk) disable iff (Reset)
    DeferIndication |=> (DeferLatched == 1'b1)
);

defer_latched_clear_on_rst : assert property (
    @(posedge MTxClk) disable iff (Reset)
    (~DeferIndication && RstDeferLatched) |=> (DeferLatched == 1'b0)
);

// -------------------------------------------------------------------------
// CarrierSenseLost assertions
// -------------------------------------------------------------------------

carrier_sense_lost_reset : assert property (
    @(posedge MTxClk) Reset |=> (CarrierSenseLost == 1'b0)
);

carrier_sense_lost_set_condition : assert property (
    @(posedge MTxClk) disable iff (Reset)
    ((StatePreamble || (|StateData)) && ~CarrierSense && ~Loopback && ~Collision && ~r_FullD)
    |=> (CarrierSenseLost == 1'b1)
);

carrier_sense_lost_clear_on_tx_start : assert property (
    @(posedge MTxClk) disable iff (Reset)
    (~((StatePreamble || (|StateData)) && ~CarrierSense && ~Loopback && ~Collision && ~r_FullD) && TxStartFrm)
    |=> (CarrierSenseLost == 1'b0)
);

endmodule

bind eth_macstatus eth_macstatus_assert eth_macstatus_assert_instance (.*);
