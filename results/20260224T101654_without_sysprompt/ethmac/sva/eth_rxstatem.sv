module eth_rxstatem_assert (
    input         MRxClk,
    input         Reset,
    input         MRxDV,
    input         ByteCntEq0,
    input         ByteCntGreat2,
    input         Transmitting,
    input         MRxDEq5,
    input         MRxDEqD,
    input         IFGCounterEq24,
    input         ByteCntMaxFrame,
    output [1:0]  StateData,
    output        StateIdle,
    output        StateDrop,
    output        StatePreamble,
    output        StateSFD
);

    // Recompute internal combinational signals from ports
    wire StartIdle     = ~MRxDV & (StateDrop | StatePreamble | StateSFD | (|StateData));
    wire StartPreamble = MRxDV & ~MRxDEq5 & (StateIdle & ~Transmitting);
    wire StartSFD      = MRxDV & MRxDEq5 & ((StateIdle & ~Transmitting) | StatePreamble);
    wire StartData0    = MRxDV & ((StateSFD & MRxDEqD & IFGCounterEq24) | StateData[1]);
    wire StartData1    = MRxDV & StateData[0] & (~ByteCntMaxFrame);
    wire StartDrop     = MRxDV & ((StateIdle & Transmitting) | (StateSFD & ~IFGCounterEq24 & MRxDEqD) | (StateData[0] & ByteCntMaxFrame));

    // -------------------------------------------------------------------------
    // Reset assertions (async reset checked at clock and reset edge)
    // -------------------------------------------------------------------------
    reset_stateidle_low : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StateIdle == 1'b0));

    reset_statedrop_high : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StateDrop == 1'b1));

    reset_statepreamble_low : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StatePreamble == 1'b0));

    reset_statesfd_low : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StateSFD == 1'b0));

    reset_statedata0_low : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StateData[0] == 1'b0));

    reset_statedata1_low : assert property (
        @(posedge MRxClk or posedge Reset) Reset |-> (StateData[1] == 1'b0));

    // -------------------------------------------------------------------------
    // One-hot state encoding: exactly one state active when not in reset
    // -------------------------------------------------------------------------
    one_hot_state_encoding : assert property (
        @(posedge MRxClk) disable iff (Reset)
        $onehot({StateIdle, StateDrop, StatePreamble, StateSFD, StateData[0], StateData[1]}));

    // -------------------------------------------------------------------------
    // At least one state must be active (no all-zero state after reset)
    // -------------------------------------------------------------------------
    at_least_one_state_active : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateIdle | StateDrop | StatePreamble | StateSFD | StateData[0] | StateData[1]));

    // -------------------------------------------------------------------------
    // StateIdle transition assertions
    // -------------------------------------------------------------------------
    stateidle_set_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartIdle & ~StartPreamble & ~StartSFD & ~StartDrop) |=> StateIdle);

    stateidle_cleared_on_startpreamble : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartPreamble |=> ~StateIdle);

    stateidle_cleared_on_startsfd : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartSFD |=> ~StateIdle);

    stateidle_cleared_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |=> ~StateIdle);

    stateidle_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartIdle & ~StartPreamble & ~StartSFD & ~StartDrop) |=> (StateIdle == $past(StateIdle)));

    // -------------------------------------------------------------------------
    // StateDrop transition assertions
    // -------------------------------------------------------------------------
    statedrop_set_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartDrop & ~StartIdle) |=> StateDrop);

    statedrop_cleared_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |=> ~StateDrop);

    statedrop_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartIdle & ~StartDrop) |=> (StateDrop == $past(StateDrop)));

    // -------------------------------------------------------------------------
    // StatePreamble transition assertions
    // -------------------------------------------------------------------------
    statepreamble_set_on_startpreamble : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartPreamble & ~StartSFD & ~StartIdle & ~StartDrop) |=> StatePreamble);

    statepreamble_cleared_on_startsfd : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartSFD |=> ~StatePreamble);

    statepreamble_cleared_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |=> ~StatePreamble);

    statepreamble_cleared_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |=> ~StatePreamble);

    statepreamble_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartPreamble & ~StartSFD & ~StartIdle & ~StartDrop) |=> (StatePreamble == $past(StatePreamble)));

    // -------------------------------------------------------------------------
    // StateSFD transition assertions
    // -------------------------------------------------------------------------
    statesfd_set_on_startsfd : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartSFD & ~StartPreamble & ~StartIdle & ~StartData0 & ~StartDrop) |=> StateSFD);

    statesfd_cleared_on_startpreamble : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartPreamble |=> ~StateSFD);

    statesfd_cleared_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |=> ~StateSFD);

    statesfd_cleared_on_startdata0 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData0 |=> ~StateSFD);

    statesfd_cleared_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |=> ~StateSFD);

    statesfd_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartSFD & ~StartPreamble & ~StartIdle & ~StartData0 & ~StartDrop) |=> (StateSFD == $past(StateSFD)));

    // -------------------------------------------------------------------------
    // StateData[0] transition assertions
    // -------------------------------------------------------------------------
    statedata0_set_on_startdata0 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartData0 & ~StartIdle & ~StartData1 & ~StartDrop) |=> StateData[0]);

    statedata0_cleared_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |=> ~StateData[0]);

    statedata0_cleared_on_startdata1 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData1 |=> ~StateData[0]);

    statedata0_cleared_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |=> ~StateData[0]);

    statedata0_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartData0 & ~StartIdle & ~StartData1 & ~StartDrop) |=> (StateData[0] == $past(StateData[0])));

    // -------------------------------------------------------------------------
    // StateData[1] transition assertions
    // -------------------------------------------------------------------------
    statedata1_set_on_startdata1 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StartData1 & ~StartIdle & ~StartData0 & ~StartDrop) |=> StateData[1]);

    statedata1_cleared_on_startidle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |=> ~StateData[1]);

    statedata1_cleared_on_startdata0 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData0 |=> ~StateData[1]);

    statedata1_cleared_on_startdrop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |=> ~StateData[1]);

    statedata1_stable_when_no_trigger : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (~StartData1 & ~StartIdle & ~StartData0 & ~StartDrop) |=> (StateData[1] == $past(StateData[1])));

    // -------------------------------------------------------------------------
    // Combinational logic correctness assertions
    // -------------------------------------------------------------------------
    startidle_logic_correct : assert property (
        @(posedge MRxClk)
        StartIdle == (~MRxDV & (StateDrop | StatePreamble | StateSFD | (|StateData))));

    startpreamble_logic_correct : assert property (
        @(posedge MRxClk)
        StartPreamble == (MRxDV & ~MRxDEq5 & StateIdle & ~Transmitting));

    startsfd_logic_correct : assert property (
        @(posedge MRxClk)
        StartSFD == (MRxDV & MRxDEq5 & ((StateIdle & ~Transmitting) | StatePreamble)));

    startdata0_logic_correct : assert property (
        @(posedge MRxClk)
        StartData0 == (MRxDV & ((StateSFD & MRxDEqD & IFGCounterEq24) | StateData[1])));

    startdata1_logic_correct : assert property (
        @(posedge MRxClk)
        StartData1 == (MRxDV & StateData[0] & ~ByteCntMaxFrame));

    startdrop_logic_correct : assert property (
        @(posedge MRxClk)
        StartDrop == (MRxDV & ((StateIdle & Transmitting) | (StateSFD & ~IFGCounterEq24 & MRxDEqD) | (StateData[0] & ByteCntMaxFrame))));

    // -------------------------------------------------------------------------
    // Functional / reachability properties
    // -------------------------------------------------------------------------
    startidle_requires_mrxdv_low : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |-> ~MRxDV);

    startpreamble_requires_mrxdv_high : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartPreamble |-> MRxDV);

    startpreamble_requires_not_transmitting : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartPreamble |-> ~Transmitting);

    startpreamble_only_from_idle : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartPreamble |-> StateIdle);

    startsfd_requires_mrxdeq5 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartSFD |-> MRxDEq5);

    startsfd_from_idle_or_preamble : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartSFD |-> (StateIdle | StatePreamble));

    startdata0_requires_mrxdv : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData0 |-> MRxDV);

    startdata0_from_sfd_or_data1 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData0 |-> (StateSFD | StateData[1]));

    startdata1_from_data0_only : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartData1 |-> StateData[0]);

    startdata1_not_when_maxframe : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateData[0] & ByteCntMaxFrame) |-> ~StartData1);

    startdrop_from_idle_sfd_or_data0 : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |-> (StateIdle | StateSFD | StateData[0]));

    startdrop_requires_mrxdv : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartDrop |-> MRxDV);

    idle_with_transmitting_causes_drop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateIdle & Transmitting & MRxDV) |-> StartDrop);

    data0_maxframe_causes_drop : assert property (
        @(posedge MRxClk) disable iff (Reset)
        (StateData[0] & ByteCntMaxFrame & MRxDV) |-> StartDrop);

    startidle_requires_active_state : assert property (
        @(posedge MRxClk) disable iff (Reset)
        StartIdle |-> (StateDrop | StatePreamble | StateSFD | (|StateData)));

    // -------------------------------------------------------------------------
    // Mutual exclusion of start signals that would conflict
    // -------------------------------------------------------------------------
    startidle_and_startpreamble_mutex : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ~(StartIdle & StartPreamble));

    startidle_and_startsfd_mutex : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ~(StartIdle & StartSFD));

    startidle_and_startdata0_mutex : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ~(StartIdle & StartData0));

    startidle_and_startdata1_mutex : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ~(StartIdle & StartData1));

    startidle_and_startdrop_mutex : assert property (
        @(posedge MRxClk) disable iff (Reset)
        ~(StartIdle & StartDrop));

endmodule

bind eth_rxstatem eth_rxstatem_assert eth_rxstatem_assert_instance (.*);
