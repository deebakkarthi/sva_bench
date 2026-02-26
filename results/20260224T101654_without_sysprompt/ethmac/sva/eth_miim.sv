module eth_miim_assert (
  input         Clk,
  input         Reset,
  input   [7:0] Divider,
  input  [15:0] CtrlData,
  input   [4:0] Rgad,
  input   [4:0] Fiad,
  input         NoPre,
  input         WCtrlData,
  input         RStat,
  input         ScanStat,
  input         Mdi,
  input         Mdc,
  input         Mdo,
  input         MdoEn,
  input         Busy,
  input         LinkFail,
  input         Nvalid,
  input  [15:0] Prsd,
  input         WCtrlDataStart,
  input         RStatStart,
  input         UpdateMIIRX_DATAReg
);

  // ---------- Asynchronous Reset Assertions ----------

  reset_clears_WCtrlDataStart : assert property (
    @(posedge Clk or posedge Reset)
    Reset |-> (WCtrlDataStart == 1'b0));

  reset_clears_RStatStart : assert property (
    @(posedge Clk or posedge Reset)
    Reset |-> (RStatStart == 1'b0));

  reset_clears_Nvalid : assert property (
    @(posedge Clk or posedge Reset)
    Reset |-> (Nvalid == 1'b0));

  reset_clears_UpdateMIIRX_DATAReg : assert property (
    @(posedge Clk or posedge Reset)
    Reset |-> (UpdateMIIRX_DATAReg == 1'b0));

  // ---------- Busy Signal Composition Assertions ----------

  WCtrlData_implies_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    WCtrlData |-> Busy);

  WCtrlDataStart_implies_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    WCtrlDataStart |-> Busy);

  RStat_implies_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    RStat |-> Busy);

  RStatStart_implies_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    RStatStart |-> Busy);

  Nvalid_implies_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    Nvalid |-> Busy);

  // ---------- WCtrlDataStart Behavior Assertions ----------

  WCtrlDataStart_set_3cycles_after_WCtrlData_rise_when_idle : assert property (
    @(posedge Clk) disable iff (Reset)
    ($rose(WCtrlData) && !Busy) |-> ##3 WCtrlDataStart);

  WCtrlDataStart_deasserted_when_not_busy : assert property (
    @(posedge Clk) disable iff (Reset)
    !Busy |-> !WCtrlDataStart);

  WCtrlDataStart_requires_prior_WCtrlData : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(WCtrlDataStart) |-> $past(WCtrlData, 3));

  WCtrlDataStart_not_set_without_WCtrlData_history : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(WCtrlDataStart) |-> ($past(WCtrlData, 2) || $past(WCtrlData, 3)));

  // ---------- RStatStart Behavior Assertions ----------

  RStatStart_set_3cycles_after_RStat_rise_when_idle : assert property (
    @(posedge Clk) disable iff (Reset)
    ($rose(RStat) && !Busy) |-> ##3 RStatStart);

  RStatStart_deasserted_when_not_busy : assert property (
    @(posedge Clk) disable iff (Reset)
    !Busy |-> !RStatStart);

  RStatStart_requires_prior_RStat : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(RStatStart) |-> $past(RStat, 3));

  RStatStart_not_set_without_RStat_history : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(RStatStart) |-> ($past(RStat, 2) || $past(RStat, 3)));

  // ---------- Nvalid Behavior Assertions ----------

  Nvalid_deasserted_when_not_busy : assert property (
    @(posedge Clk) disable iff (Reset)
    !Busy |-> !Nvalid);

  Nvalid_only_set_when_ScanStat_active : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(Nvalid) |-> (ScanStat || $past(ScanStat)));

  // ---------- UpdateMIIRX_DATAReg Assertions ----------

  UpdateMIIRX_DATAReg_is_single_cycle_pulse : assert property (
    @(posedge Clk) disable iff (Reset)
    UpdateMIIRX_DATAReg |=> !UpdateMIIRX_DATAReg);

  UpdateMIIRX_deasserted_during_write_operation : assert property (
    @(posedge Clk) disable iff (Reset)
    WCtrlDataStart |-> !UpdateMIIRX_DATAReg);

  UpdateMIIRX_deasserted_when_not_busy : assert property (
    @(posedge Clk) disable iff (Reset)
    !Busy |-> !UpdateMIIRX_DATAReg);

  UpdateMIIRX_only_set_after_busy : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(UpdateMIIRX_DATAReg) |-> $past(Busy));

  // ---------- Operational Mutual Exclusion Assertions ----------

  UpdateMIIRX_not_concurrent_with_WCtrlDataStart : assert property (
    @(posedge Clk) disable iff (Reset)
    !(WCtrlDataStart && UpdateMIIRX_DATAReg));

  WCtrlDataStart_falls_only_during_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    $fell(WCtrlDataStart) |-> $past(Busy));

  RStatStart_falls_only_during_Busy : assert property (
    @(posedge Clk) disable iff (Reset)
    $fell(RStatStart) |-> $past(Busy));

  // ---------- Busy Stability Assertions ----------

  Busy_rises_with_WCtrlData_or_RStat_or_ScanStat : assert property (
    @(posedge Clk) disable iff (Reset)
    $rose(Busy) |-> (WCtrlData || RStat || ScanStat ||
                     $past(WCtrlData) || $past(RStat) || $past(ScanStat)));

  Nvalid_stable_when_busy_and_no_operation_end : assert property (
    @(posedge Clk) disable iff (Reset)
    (Nvalid && Busy && !$rose(Busy)) |=>
    (Nvalid || !Busy));

endmodule

bind eth_miim eth_miim_assert eth_miim_assert_instance (.*);
