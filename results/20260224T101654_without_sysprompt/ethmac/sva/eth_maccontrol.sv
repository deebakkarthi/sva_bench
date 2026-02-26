module eth_maccontrol_assert (
    input         MTxClk,
    input         MRxClk,
    input         TxReset,
    input         RxReset,
    input         TPauseRq,
    input   [7:0] TxDataIn,
    input         TxStartFrmIn,
    input         TxUsedDataIn,
    input         TxEndFrmIn,
    input         TxDoneIn,
    input         TxAbortIn,
    input         PadIn,
    input         CrcEnIn,
    input   [7:0] RxData,
    input         RxValid,
    input         RxStartFrm,
    input         RxEndFrm,
    input         ReceiveEnd,
    input         ReceivedPacketGood,
    input         ReceivedLengthOK,
    input         TxFlow,
    input         RxFlow,
    input         DlyCrcEn,
    input  [15:0] TxPauseTV,
    input  [47:0] MAC,
    input         RxStatusWriteLatched_sync2,
    input         r_PassAll,
    input   [7:0] TxDataOut,
    input         TxStartFrmOut,
    input         TxEndFrmOut,
    input         TxDoneOut,
    input         TxAbortOut,
    input         TxUsedDataOut,
    input         PadOut,
    input         CrcEnOut,
    input         WillSendControlFrame,
    input         TxCtrlEndFrm,
    input         ReceivedPauseFrm,
    input         ControlFrmAddressOK,
    input         SetPauseTimer
);

    // Internal signal references via hierarchical paths
    wire CtrlMux             = eth_maccontrol_assert_instance.CtrlMux;
    wire TxCtrlStartFrm      = eth_maccontrol_assert_instance.TxCtrlStartFrm;
    wire Pause               = eth_maccontrol_assert_instance.Pause;
    wire SendingCtrlFrm      = eth_maccontrol_assert_instance.SendingCtrlFrm;
    wire BlockTxDone         = eth_maccontrol_assert_instance.BlockTxDone;
    wire [7:0] ControlData   = eth_maccontrol_assert_instance.ControlData;
    wire TxUsedDataOutDetected = eth_maccontrol_assert_instance.TxUsedDataOutDetected;
    wire TxAbortInLatched    = eth_maccontrol_assert_instance.TxAbortInLatched;
    wire TxDoneInLatched     = eth_maccontrol_assert_instance.TxDoneInLatched;
    wire MuxedAbort          = eth_maccontrol_assert_instance.MuxedAbort;
    wire MuxedDone           = eth_maccontrol_assert_instance.MuxedDone;

    // -----------------------------------------------------------------------
    // TxUsedDataOutDetected: reset to 0 on TxReset
    // -----------------------------------------------------------------------
    TxUsedDataOutDetected_reset : assert property (
        @(posedge MTxClk)
        TxReset |=> (TxUsedDataOutDetected == 1'b0)
    );

    // TxUsedDataOutDetected: cleared on TxDoneIn
    TxUsedDataOutDetected_clear_on_TxDoneIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxDoneIn |=> (TxUsedDataOutDetected == 1'b0)
    );

    // TxUsedDataOutDetected: cleared on TxAbortIn
    TxUsedDataOutDetected_clear_on_TxAbortIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxAbortIn |=> (TxUsedDataOutDetected == 1'b0)
    );

    // TxUsedDataOutDetected: set when TxUsedDataOut asserted and no done/abort
    TxUsedDataOutDetected_set_on_TxUsedDataOut : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (TxUsedDataOut && !TxDoneIn && !TxAbortIn) |=> (TxUsedDataOutDetected == 1'b1)
    );

    // TxUsedDataOutDetected: stable when no relevant event
    TxUsedDataOutDetected_stable : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!TxDoneIn && !TxAbortIn && !TxUsedDataOut) |=>
        ($stable(TxUsedDataOutDetected))
    );

    // -----------------------------------------------------------------------
    // TxAbortInLatched: reset to 0 on TxReset
    // -----------------------------------------------------------------------
    TxAbortInLatched_reset : assert property (
        @(posedge MTxClk)
        TxReset |=> (TxAbortInLatched == 1'b0)
    );

    // TxAbortInLatched: tracks TxAbortIn with one cycle delay
    TxAbortInLatched_tracks_TxAbortIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        1'b1 |=> (TxAbortInLatched == $past(TxAbortIn))
    );

    // -----------------------------------------------------------------------
    // TxDoneInLatched: reset to 0 on TxReset
    // -----------------------------------------------------------------------
    TxDoneInLatched_reset : assert property (
        @(posedge MTxClk)
        TxReset |=> (TxDoneInLatched == 1'b0)
    );

    // TxDoneInLatched: tracks TxDoneIn with one cycle delay
    TxDoneInLatched_tracks_TxDoneIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        1'b1 |=> (TxDoneInLatched == $past(TxDoneIn))
    );

    // -----------------------------------------------------------------------
    // MuxedAbort: reset to 0 on TxReset
    // -----------------------------------------------------------------------
    MuxedAbort_reset : assert property (
        @(posedge MTxClk)
        TxReset |=> (MuxedAbort == 1'b0)
    );

    // MuxedAbort: cleared on TxStartFrmIn
    MuxedAbort_clear_on_TxStartFrmIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxStartFrmIn |=> (MuxedAbort == 1'b0)
    );

    // MuxedAbort: set on rising edge of TxAbortIn when TxUsedDataOutDetected
    MuxedAbort_set_condition : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!TxStartFrmIn && TxAbortIn && !TxAbortInLatched && TxUsedDataOutDetected) |=>
        (MuxedAbort == 1'b1)
    );

    // MuxedAbort: stable when no relevant event
    MuxedAbort_stable : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!TxStartFrmIn && !(TxAbortIn && !TxAbortInLatched && TxUsedDataOutDetected)) |=>
        ($stable(MuxedAbort))
    );

    // -----------------------------------------------------------------------
    // MuxedDone: reset to 0 on TxReset
    // -----------------------------------------------------------------------
    MuxedDone_reset : assert property (
        @(posedge MTxClk)
        TxReset |=> (MuxedDone == 1'b0)
    );

    // MuxedDone: cleared on TxStartFrmIn
    MuxedDone_clear_on_TxStartFrmIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxStartFrmIn |=> (MuxedDone == 1'b0)
    );

    // MuxedDone: set on rising edge of TxDoneIn when TxUsedDataOutDetected
    MuxedDone_set_condition : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!TxStartFrmIn && TxDoneIn && !TxDoneInLatched && TxUsedDataOutDetected) |=>
        (MuxedDone == 1'b1)
    );

    // MuxedDone: stable when no relevant event
    MuxedDone_stable : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!TxStartFrmIn && !(TxDoneIn && !TxDoneInLatched && TxUsedDataOutDetected)) |=>
        ($stable(MuxedDone))
    );

    // -----------------------------------------------------------------------
    // TxDoneOut combinational: CtrlMux path
    // -----------------------------------------------------------------------
    TxDoneOut_ctrlmux_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |->
        (TxDoneOut == (~TxStartFrmIn & ~BlockTxDone & MuxedDone))
    );

    // TxDoneOut combinational: non-CtrlMux path
    TxDoneOut_normal_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |->
        (TxDoneOut == (~TxStartFrmIn & ~BlockTxDone & TxDoneIn))
    );

    // -----------------------------------------------------------------------
    // TxAbortOut combinational: CtrlMux path
    // -----------------------------------------------------------------------
    TxAbortOut_ctrlmux_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |->
        (TxAbortOut == (~TxStartFrmIn & ~BlockTxDone & MuxedAbort))
    );

    // TxAbortOut combinational: non-CtrlMux path
    TxAbortOut_normal_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |->
        (TxAbortOut == (~TxStartFrmIn & ~BlockTxDone & TxAbortIn))
    );

    // -----------------------------------------------------------------------
    // TxUsedDataOut: blocked when CtrlMux active
    // -----------------------------------------------------------------------
    TxUsedDataOut_blocked_when_ctrlmux : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |-> (TxUsedDataOut == 1'b0)
    );

    // TxUsedDataOut: equals TxUsedDataIn when not CtrlMux
    TxUsedDataOut_passthrough_when_not_ctrlmux : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |-> (TxUsedDataOut == TxUsedDataIn)
    );

    // -----------------------------------------------------------------------
    // TxStartFrmOut: CtrlMux path uses TxCtrlStartFrm
    // -----------------------------------------------------------------------
    TxStartFrmOut_ctrlmux_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |-> (TxStartFrmOut == TxCtrlStartFrm)
    );

    // TxStartFrmOut: non-CtrlMux path gated by Pause
    TxStartFrmOut_normal_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |-> (TxStartFrmOut == (TxStartFrmIn & ~Pause))
    );

    // TxStartFrmOut: blocked when Pause asserted and not CtrlMux
    TxStartFrmOut_blocked_by_pause : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (!CtrlMux && Pause) |-> (TxStartFrmOut == 1'b0)
    );

    // -----------------------------------------------------------------------
    // TxEndFrmOut: CtrlMux path uses TxCtrlEndFrm
    // -----------------------------------------------------------------------
    TxEndFrmOut_ctrlmux_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |-> (TxEndFrmOut == TxCtrlEndFrm)
    );

    // TxEndFrmOut: non-CtrlMux path uses TxEndFrmIn
    TxEndFrmOut_normal_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |-> (TxEndFrmOut == TxEndFrmIn)
    );

    // -----------------------------------------------------------------------
    // TxDataOut: CtrlMux path uses ControlData
    // -----------------------------------------------------------------------
    TxDataOut_ctrlmux_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        CtrlMux |-> (TxDataOut == ControlData)
    );

    // TxDataOut: non-CtrlMux path uses TxDataIn
    TxDataOut_normal_path : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !CtrlMux |-> (TxDataOut == TxDataIn)
    );

    // -----------------------------------------------------------------------
    // PadOut: OR of PadIn and SendingCtrlFrm
    // -----------------------------------------------------------------------
    PadOut_logic : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (PadOut == (PadIn | SendingCtrlFrm))
    );

    // PadOut: asserted when SendingCtrlFrm
    PadOut_asserted_when_sending_ctrl : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        SendingCtrlFrm |-> PadOut
    );

    // PadOut: follows PadIn when not SendingCtrlFrm
    PadOut_follows_PadIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !SendingCtrlFrm |-> (PadOut == PadIn)
    );

    // -----------------------------------------------------------------------
    // CrcEnOut: OR of CrcEnIn and SendingCtrlFrm
    // -----------------------------------------------------------------------
    CrcEnOut_logic : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        (CrcEnOut == (CrcEnIn | SendingCtrlFrm))
    );

    // CrcEnOut: asserted when SendingCtrlFrm
    CrcEnOut_asserted_when_sending_ctrl : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        SendingCtrlFrm |-> CrcEnOut
    );

    // CrcEnOut: follows CrcEnIn when not SendingCtrlFrm
    CrcEnOut_follows_CrcEnIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !SendingCtrlFrm |-> (CrcEnOut == CrcEnIn)
    );

    // -----------------------------------------------------------------------
    // TxDoneOut and TxAbortOut mutually exclusive
    // -----------------------------------------------------------------------
    TxDoneOut_TxAbortOut_mutually_exclusive : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !(TxDoneOut && TxAbortOut)
    );

    // -----------------------------------------------------------------------
    // TxDoneOut deasserted when TxStartFrmIn
    // -----------------------------------------------------------------------
    TxDoneOut_deasserted_on_TxStartFrmIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxStartFrmIn |-> !TxDoneOut
    );

    // -----------------------------------------------------------------------
    // TxAbortOut deasserted when TxStartFrmIn
    // -----------------------------------------------------------------------
    TxAbortOut_deasserted_on_TxStartFrmIn : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        TxStartFrmIn |-> !TxAbortOut
    );

    // -----------------------------------------------------------------------
    // TxDoneOut deasserted when BlockTxDone
    // -----------------------------------------------------------------------
    TxDoneOut_deasserted_when_BlockTxDone : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        BlockTxDone |-> !TxDoneOut
    );

    // -----------------------------------------------------------------------
    // TxAbortOut deasserted when BlockTxDone
    // -----------------------------------------------------------------------
    TxAbortOut_deasserted_when_BlockTxDone : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        BlockTxDone |-> !TxAbortOut
    );

    // -----------------------------------------------------------------------
    // TxUsedDataOut never asserted simultaneously with CtrlMux
    // -----------------------------------------------------------------------
    TxUsedDataOut_not_with_CtrlMux : assert property (
        @(posedge MTxClk) disable iff (TxReset)
        !(TxUsedDataOut && CtrlMux)
    );

endmodule

bind eth_maccontrol eth_maccontrol_assert eth_maccontrol_assert_instance (.*);
