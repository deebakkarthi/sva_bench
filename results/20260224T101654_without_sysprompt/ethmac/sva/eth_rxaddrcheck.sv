module eth_rxaddrcheck_assert (
  input        MRxClk,
  input        Reset,
  input [7:0]  RxData,
  input        Broadcast,
  input        r_Bro,
  input        r_Pro,
  input        ByteCntEq0,
  input        ByteCntEq2,
  input        ByteCntEq3,
  input        ByteCntEq4,
  input        ByteCntEq5,
  input        ByteCntEq6,
  input        ByteCntEq7,
  input [31:0] HASH0,
  input [31:0] HASH1,
  input [5:0]  CrcHash,
  input        CrcHashGood,
  input        Multicast,
  input [47:0] MAC,
  input [1:0]  StateData,
  input        RxEndFrm,
  input        PassAll,
  input        ControlFrmAddressOK,
  output       RxAbort,
  output       AddressMiss
);

  // Async reset: at any posedge where Reset is sampled high, outputs must already be cleared
  reset_clears_RxAbort_async : assert property (
    @(posedge MRxClk)
    Reset |-> !RxAbort);

  reset_clears_AddressMiss_async : assert property (
    @(posedge MRxClk)
    Reset |-> !AddressMiss);

  // RxAbort is always cleared the cycle after ByteCntEq7 & RxCheckEn is not active
  RxAbort_cleared_without_check_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    !(ByteCntEq7 & (|StateData)) |=> !RxAbort);

  // RxAbort can only rise after a cycle where ByteCntEq7 and RxCheckEn were both asserted
  RxAbort_only_rises_after_ByteCntEq7_RxCheckEn : assert property (
    @(posedge MRxClk) disable iff (Reset)
    $rose(RxAbort) |-> $past(ByteCntEq7 & (|StateData)));

  // Promiscuous mode (r_Pro) prevents RxAbort because it makes RxAddressInvalid false
  promiscuous_mode_prevents_RxAbort : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (ByteCntEq7 & (|StateData) & r_Pro) |=> !RxAbort);

  // Valid broadcast (Broadcast & ~r_Bro = BroadcastOK) prevents RxAbort
  broadcast_ok_prevents_RxAbort : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (ByteCntEq7 & (|StateData) & Broadcast & ~r_Bro) |=> !RxAbort);

  // StateData == 0 means RxCheckEn is deasserted, so RxAbort is never set
  no_rxchecken_clears_RxAbort : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (StateData == 2'b00) |=> !RxAbort);

  // AddressMiss is cleared when ByteCntEq0 signals start of a new frame
  AddressMiss_cleared_by_ByteCntEq0 : assert property (
    @(posedge MRxClk) disable iff (Reset)
    ByteCntEq0 |=> !AddressMiss);

  // AddressMiss holds its value when neither ByteCntEq0 nor ByteCntEq7 & RxCheckEn
  AddressMiss_stable_when_no_update_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    !(ByteCntEq0 | (ByteCntEq7 & (|StateData))) |=>
    (AddressMiss == $past(AddressMiss)));

  // AddressMiss can only rise after a cycle where ByteCntEq7 & RxCheckEn was active and ByteCntEq0 was not
  AddressMiss_only_set_after_ByteCntEq7_RxCheckEn : assert property (
    @(posedge MRxClk) disable iff (Reset)
    $rose(AddressMiss) |-> $past(ByteCntEq7 & (|StateData) & !ByteCntEq0));

  // PassAll & ControlFrmAddressOK prevents AddressMiss from being set at byte 7
  passall_cfaok_prevents_AddressMiss : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (ByteCntEq7 & (|StateData) & PassAll & ControlFrmAddressOK & !ByteCntEq0) |=>
    !AddressMiss);

  // Valid broadcast (BroadcastOK) prevents AddressMiss from being set at byte 7
  broadcast_ok_prevents_AddressMiss : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (ByteCntEq7 & (|StateData) & Broadcast & ~r_Bro & !ByteCntEq0) |=>
    !AddressMiss);

  // ByteCntEq0 has priority over ByteCntEq7 for AddressMiss (code structure)
  ByteCntEq0_priority_over_ByteCntEq7_for_AddressMiss : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (ByteCntEq0 & ByteCntEq7 & (|StateData)) |=> !AddressMiss);

  // End-to-end: if all 6 consecutive address bytes match the MAC, RxAbort must not be set
  unicast_match_prevents_RxAbort : assert property (
    @(posedge MRxClk) disable iff (Reset)
    ((|StateData) & ByteCntEq2 & (RxData == MAC[47:40]))
    ##1 ((|StateData) & ByteCntEq3 & (RxData == MAC[39:32]))
    ##1 ((|StateData) & ByteCntEq4 & (RxData == MAC[31:24]))
    ##1 ((|StateData) & ByteCntEq5 & (RxData == MAC[23:16]))
    ##1 ((|StateData) & ByteCntEq6 & (RxData == MAC[15:8]))
    ##1 ((|StateData) & ByteCntEq7 & (RxData == MAC[7:0]))
    |=> !RxAbort);

  // End-to-end: if all 6 consecutive address bytes match the MAC, AddressMiss must not be set
  unicast_match_prevents_AddressMiss : assert property (
    @(posedge MRxClk) disable iff (Reset)
    ((|StateData) & ByteCntEq2 & (RxData == MAC[47:40]))
    ##1 ((|StateData) & ByteCntEq3 & (RxData == MAC[39:32]))
    ##1 ((|StateData) & ByteCntEq4 & (RxData == MAC[31:24]))
    ##1 ((|StateData) & ByteCntEq5 & (RxData == MAC[23:16]))
    ##1 ((|StateData) & ByteCntEq6 & (RxData == MAC[15:8]))
    ##1 ((|StateData) & ByteCntEq7 & (RxData == MAC[7:0]) & !ByteCntEq0)
    |=> !AddressMiss);

  // RxAbort is a single-cycle pulse: if ByteCntEq7 & RxCheckEn holds for two consecutive cycles
  // and address was invalid both times, RxAbort remains asserted; otherwise it clears
  RxAbort_clears_next_cycle_without_repeat_condition : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (RxAbort & !(ByteCntEq7 & (|StateData))) |=> !RxAbort);

  // r_Pro does not appear in AddressMiss logic, so promiscuous mode alone cannot suppress AddressMiss
  // Verified indirectly: AddressMiss update expression uses PassAll&ControlFrmAddressOK not r_Pro
  // When at ByteCntEq7 with RxCheckEn and PassAll & ControlFrmAddressOK is false, r_Pro has no effect:
  // Cannot assert "r_Pro does NOT prevent AddressMiss" without internals, but
  // we can assert that AddressMiss can still rise even when r_Pro is set
  // (no assertion needed; the absence of r_Pro from AddressMiss logic is structural)

  // Mutual exclusivity of ByteCntEq signals is assumed external; here we verify no
  // spurious RxAbort when StateData is zero regardless of other inputs
  rxabort_never_set_in_idle_state : assert property (
    @(posedge MRxClk) disable iff (Reset)
    (StateData == 2'b00) ##1 (StateData == 2'b00) |-> !RxAbort);

endmodule

bind eth_rxaddrcheck eth_rxaddrcheck_assert eth_rxaddrcheck_assert_instance (.*);
