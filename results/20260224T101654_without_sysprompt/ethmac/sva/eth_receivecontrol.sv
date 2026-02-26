module eth_receivecontrol_assert (
    input       MTxClk,
    input       MRxClk,
    input       TxReset,
    input       RxReset,
    input [7:0] RxData,
    input       RxValid,
    input       RxStartFrm,
    input       RxEndFrm,
    input       RxFlow,
    input       ReceiveEnd,
    input [47:0]MAC,
    input       DlyCrcEn,
    input       TxDoneIn,
    input       TxAbortIn,
    input       TxStartFrmOut,
    input       ReceivedLengthOK,
    input       ReceivedPacketGood,
    input       TxUsedDataOutDetected,
    input       RxStatusWriteLatched_sync2,
    input       r_PassAll,
    output      Pause,
    output      ReceivedPauseFrm,
    output      AddressOK,
    output      SetPauseTimer
);

    // ---------------------------------------------------------------
    // Reset behaviour (asynchronous): while RxReset is asserted the
    // sampled output must already be at its reset value.
    // ---------------------------------------------------------------
    rx_reset_AddressOK_low :
        assert property (@(posedge MRxClk)
            RxReset |-> !AddressOK);

    rx_reset_ReceivedPauseFrm_low :
        assert property (@(posedge MRxClk)
            RxReset |-> !ReceivedPauseFrm);

    tx_reset_Pause_low :
        assert property (@(posedge MTxClk)
            TxReset |-> !Pause);

    // ---------------------------------------------------------------
    // AddressOK must be de-asserted one cycle after ReceiveEnd
    // (when not in reset)
    // ---------------------------------------------------------------
    AddressOK_clears_after_ReceiveEnd :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            ReceiveEnd |=> !AddressOK);

    // ---------------------------------------------------------------
    // ReceivedPauseFrm: cleared the cycle after the PassAll condition
    // ---------------------------------------------------------------
    ReceivedPauseFrm_clears_on_passall_write :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            (RxStatusWriteLatched_sync2 & r_PassAll) |=> !ReceivedPauseFrm);

    ReceivedPauseFrm_clears_when_no_passall :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            (ReceivedPauseFrm & ~r_PassAll) |=> !ReceivedPauseFrm);

    // ---------------------------------------------------------------
    // ReceivedPauseFrm cannot be set unless RxValid was seen
    // ---------------------------------------------------------------
    ReceivedPauseFrm_requires_RxValid_history :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            $rose(ReceivedPauseFrm) |-> $past(RxValid, 1));

    // ---------------------------------------------------------------
    // SetPauseTimer is purely combinational: every required condition
    // must hold whenever it is asserted.
    // ---------------------------------------------------------------
    SetPauseTimer_requires_ReceiveEnd :
        assert property (@(posedge MRxClk)
            SetPauseTimer |-> ReceiveEnd);

    SetPauseTimer_requires_RxFlow :
        assert property (@(posedge MRxClk)
            SetPauseTimer |-> RxFlow);

    SetPauseTimer_requires_ReceivedPacketGood :
        assert property (@(posedge MRxClk)
            SetPauseTimer |-> ReceivedPacketGood);

    SetPauseTimer_requires_ReceivedLengthOK :
        assert property (@(posedge MRxClk)
            SetPauseTimer |-> ReceivedLengthOK);

    // SetPauseTimer can only fire on the same cycle as ReceiveEnd
    SetPauseTimer_only_on_ReceiveEnd_pulse :
        assert property (@(posedge MRxClk)
            !ReceiveEnd |-> !SetPauseTimer);

    // ---------------------------------------------------------------
    // Pause: de-asserted immediately after TxReset (async)
    // ---------------------------------------------------------------
    Pause_low_during_tx_reset :
        assert property (@(posedge MTxClk)
            TxReset |-> !Pause);

    // Pause can only be high when RxFlow is high (it is set to
    // RxFlow & ~PauseTimerEq0_sync2)
    Pause_requires_RxFlow :
        assert property (@(posedge MTxClk) disable iff (TxReset)
            Pause |-> RxFlow);

    // Once an update condition fires and RxFlow=0, Pause must drop
    Pause_clears_when_RxFlow_low_on_update :
        assert property (@(posedge MTxClk) disable iff (TxReset)
            ((TxDoneIn | TxAbortIn | ~TxUsedDataOutDetected) & ~TxStartFrmOut & ~RxFlow)
            |=> !Pause);

    // Pause stays stable when no update condition is active and no reset
    Pause_stable_without_update :
        assert property (@(posedge MTxClk) disable iff (TxReset)
            (~(TxDoneIn | TxAbortIn | ~TxUsedDataOutDetected) | TxStartFrmOut)
            |=> Pause == $past(Pause));

    // ---------------------------------------------------------------
    // AddressOK: once cleared, stays 0 until the first valid byte of
    // the next frame (DetectionWindow & ByteCntEq0 active)
    // ---------------------------------------------------------------
    AddressOK_stable_zero_after_ReceiveEnd :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            (!AddressOK && !RxValid) |=> !AddressOK);

    // ---------------------------------------------------------------
    // ReceivedPauseFrm: stable when no modifying condition
    // ---------------------------------------------------------------
    ReceivedPauseFrm_no_spurious_set :
        assert property (@(posedge MRxClk) disable iff (RxReset)
            $rose(ReceivedPauseFrm) |->
                $past(RxValid) && ($past(ReceivedPauseFrm) == 1'b0));

    // ---------------------------------------------------------------
    // SetPauseTimer must not fire without ReceivedPauseFrm being
    // eventually true (it depends on ReceivedPauseFrmWAddr which
    // tracks a superset; at minimum Pause control requires a pause frm)
    // ---------------------------------------------------------------
    SetPauseTimer_only_after_RxFlow_and_GoodPacket :
        assert property (@(posedge MRxClk)
            SetPauseTimer |-> ReceivedLengthOK & ReceivedPacketGood & RxFlow & ReceiveEnd);

    // ---------------------------------------------------------------
    // RxReset releases: outputs should remain 0 the very first cycle
    // after reset is de-asserted (they were held at 0 during reset)
    // ---------------------------------------------------------------
    AddressOK_zero_first_cycle_after_rx_reset :
        assert property (@(posedge MRxClk)
            $fell(RxReset) |-> !AddressOK);

    ReceivedPauseFrm_zero_first_cycle_after_rx_reset :
        assert property (@(posedge MRxClk)
            $fell(RxReset) |-> !ReceivedPauseFrm);

    Pause_zero_first_cycle_after_tx_reset :
        assert property (@(posedge MTxClk)
            $fell(TxReset) |-> !Pause);

    // ---------------------------------------------------------------
    // SetPauseTimer is a level signal, not a registered one;
    // it must de-assert within one cycle when ReceiveEnd drops
    // ---------------------------------------------------------------
    SetPauseTimer_deasserts_after_ReceiveEnd :
        assert property (@(posedge MRxClk)
            $fell(ReceiveEnd) |=> !SetPauseTimer);

endmodule

bind eth_receivecontrol eth_receivecontrol_assert eth_receivecontrol_assert_instance (.*);
