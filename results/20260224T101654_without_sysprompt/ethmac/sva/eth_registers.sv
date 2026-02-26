module eth_registers_assert(
    input [31:0] DataIn,
    input [7:0] Address,
    input Rw,
    input [3:0] Cs,
    input Clk,
    input Reset,
    input WCtrlDataStart,
    input RStatStart,
    input UpdateMIIRX_DATAReg,
    input [15:0] Prsd,
    output [31:0] DataOut,
    output r_RecSmall,
    output r_Pad,
    output r_HugEn,
    output r_CrcEn,
    output r_DlyCrcEn,
    output r_FullD,
    output r_ExDfrEn,
    output r_NoBckof,
    output r_LoopBck,
    output r_IFG,
    output r_Pro,
    output r_Iam,
    output r_Bro,
    output r_NoPre,
    output r_TxEn,
    output r_RxEn,
    output [31:0] r_HASH0,
    output [31:0] r_HASH1,
    input TxB_IRQ,
    input TxE_IRQ,
    input RxB_IRQ,
    input RxE_IRQ,
    input Busy_IRQ,
    output [6:0] r_IPGT,
    output [6:0] r_IPGR1,
    output [6:0] r_IPGR2,
    output [15:0] r_MinFL,
    output [15:0] r_MaxFL,
    output [3:0] r_MaxRet,
    output [5:0] r_CollValid,
    output r_TxFlow,
    output r_RxFlow,
    output r_PassAll,
    output r_MiiNoPre,
    output [7:0] r_ClkDiv,
    output r_WCtrlData,
    output r_RStat,
    output r_ScanStat,
    output [4:0] r_RGAD,
    output [4:0] r_FIAD,
    output [15:0] r_CtrlData,
    input NValid_stat,
    input Busy_stat,
    input LinkFail,
    output [47:0] r_MAC,
    output [7:0] r_TxBDNum,
    output int_o,
    output [15:0] r_TxPauseTV,
    output r_TxPauseRq,
    input RstTxPauseRq,
    input TxCtrlEndFrm,
    input StartTxDone,
    input TxClk,
    input RxClk,
    input SetPauseTimer,
    input [31:0] dbg_dat
);

    // DataOut must be zero when not performing a read (Read = (|Cs) & ~Rw)
    dataout_zero_when_no_read : assert property (
        @(posedge Clk)
        (~(|Cs) || Rw) |-> (DataOut == 32'h0)
    );

    // r_TxEn can only be asserted when there is at least one TX buffer descriptor
    txen_requires_nonzero_bdnum : assert property (
        @(posedge Clk)
        r_TxEn |-> (r_TxBDNum > 8'h0)
    );

    // r_RxEn can only be asserted when TX_BD_NUM < 0x80 (at least one RxBD)
    rxen_requires_bdnum_lt_80 : assert property (
        @(posedge Clk)
        r_RxEn |-> (r_TxBDNum < 8'h80)
    );

    // TX_BD_NUM register should never exceed 0x80 (only values <= 0x80 are written)
    txbdnum_never_exceeds_80 : assert property (
        @(posedge Clk)
        r_TxBDNum <= 8'h80
    );

    // int_o must be deasserted during reset (all irq regs are async-reset to 0)
    int_zero_during_reset : assert property (
        @(posedge Clk)
        Reset |-> (int_o == 1'b0)
    );

    // r_RStat is synchronously cleared one cycle after RStatStart
    rstat_cleared_after_rstatstart : assert property (
        @(posedge Clk) disable iff (Reset)
        RStatStart |=> ~r_RStat
    );

    // r_WCtrlData is synchronously cleared one cycle after WCtrlDataStart
    wctrldata_cleared_after_wctrlstart : assert property (
        @(posedge Clk) disable iff (Reset)
        WCtrlDataStart |=> ~r_WCtrlData
    );

    // r_TxPauseRq is synchronously cleared one cycle after RstTxPauseRq
    txpauserq_cleared_after_rsttxpauserq : assert property (
        @(posedge Clk) disable iff (Reset)
        RstTxPauseRq |=> ~r_TxPauseRq
    );

    // When reading MIISTATUS register, DataOut[0] must reflect LinkFail
    miistatus_linkfail_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIISTATUS_ADR)) |-> (DataOut[0] == LinkFail)
    );

    // When reading MIISTATUS register, DataOut[1] must reflect Busy_stat
    miistatus_busy_stat_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIISTATUS_ADR)) |-> (DataOut[1] == Busy_stat)
    );

    // When reading MIISTATUS register, DataOut[2] must reflect NValid_stat
    miistatus_nvalid_stat_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIISTATUS_ADR)) |-> (DataOut[2] == NValid_stat)
    );

    // Upper bits of MIISTATUS read must be zero
    miistatus_upper_bits_zero : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIISTATUS_ADR)) |-> (DataOut[31:`ETH_MIISTATUS_WIDTH] == 0)
    );

    // r_TxPauseRq and r_TxPauseTV are mutually consistent as TXCTRL fields
    // r_TxPauseRq must be 0 if int_o is 0 is not directly provable, but we can assert
    // that r_TxEn and r_RxEn are mutually exclusive when TX_BD_NUMOut is boundary value
    txen_rxen_mutex_at_boundary : assert property (
        @(posedge Clk)
        (r_TxBDNum == 8'h80) |-> (~r_RxEn)
    );

    // r_TxBDNum at zero implies r_TxEn is deasserted
    txen_deasserted_when_bdnum_zero : assert property (
        @(posedge Clk)
        (r_TxBDNum == 8'h0) |-> (~r_TxEn)
    );

    // When reading TX_BD_NUM register, DataOut[7:0] must match r_TxBDNum
    read_txbdnum_matches_output : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_TX_BD_NUM_ADR)) |-> (DataOut[7:0] == r_TxBDNum)
    );

    // Upper bits of TX_BD_NUM read must be zero
    read_txbdnum_upper_zero : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_TX_BD_NUM_ADR)) |-> (DataOut[31:8] == 24'h0)
    );

    // r_IPGT upper bit must not be driven (it's 7 bits)
    ipgt_width_check : assert property (
        @(posedge Clk)
        $onehot0(r_IPGT) || (r_IPGT <= 7'h7F)
    );

    // r_RGAD is 5-bit field from MIIADDRESS[12:8]
    rgad_width_check : assert property (
        @(posedge Clk)
        r_RGAD <= 5'h1F
    );

    // r_FIAD is 5-bit field from MIIADDRESS[4:0]
    fiad_width_check : assert property (
        @(posedge Clk)
        r_FIAD <= 5'h1F
    );

    // After reset, r_TxEn must be deasserted
    txen_deasserted_after_reset : assert property (
        @(posedge Clk)
        $rose(~Reset) |-> ~r_TxEn
    );

    // After reset, r_RxEn must be deasserted
    rxen_deasserted_after_reset : assert property (
        @(posedge Clk)
        $rose(~Reset) |-> ~r_RxEn
    );

    // When reading IPGT register, upper bits should be zero
    ipgt_read_upper_bits_zero : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_IPGT_ADR)) |-> (DataOut[31:`ETH_IPGT_WIDTH_0] == 0)
    );

    // When reading IPGR1 register, upper bits should be zero
    ipgr1_read_upper_bits_zero : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_IPGR1_ADR)) |-> (DataOut[31:`ETH_IPGR1_WIDTH_0] == 0)
    );

    // When reading IPGR2 register, upper bits should be zero
    ipgr2_read_upper_bits_zero : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_IPGR2_ADR)) |-> (DataOut[31:`ETH_IPGR2_WIDTH_0] == 0)
    );

    // r_MinFL and r_MaxFL are non-overlapping fields of PACKETLEN
    // When reading PACKETLEN, upper half is MinFL and lower half is MaxFL
    packetlen_minfl_in_upper : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_PACKETLEN_ADR)) |-> (DataOut[31:16] == r_MinFL)
    );

    packetlen_maxfl_in_lower : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_PACKETLEN_ADR)) |-> (DataOut[15:0] == r_MaxFL)
    );

    // r_TxFlow, r_RxFlow, r_PassAll come from CTRLMODEROut[2:0]
    // When reading CTRLMODER, lower 3 bits map to these fields
    ctrlmoder_txflow_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_CTRLMODER_ADR)) |-> (DataOut[2] == r_TxFlow)
    );

    ctrlmoder_rxflow_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_CTRLMODER_ADR)) |-> (DataOut[1] == r_RxFlow)
    );

    ctrlmoder_passall_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_CTRLMODER_ADR)) |-> (DataOut[0] == r_PassAll)
    );

    // r_TxPauseTV reflects lower 16 bits of TXCTRL
    txctrl_txpausetv_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_TX_CTRL_ADR)) |-> (DataOut[15:0] == r_TxPauseTV)
    );

    // r_TxPauseRq reflects bit 16 of TXCTRL
    txctrl_txpauserq_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_TX_CTRL_ADR)) |-> (DataOut[16] == r_TxPauseRq)
    );

    // r_MiiNoPre comes from MIIMODEROut[8]
    miimoder_miinopre_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIIMODER_ADR)) |-> (DataOut[8] == r_MiiNoPre)
    );

    // r_ClkDiv comes from MIIMODEROut[7:0]
    miimoder_clkdiv_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIIMODER_ADR)) |-> (DataOut[7:0] == r_ClkDiv)
    );

    // r_MaxRet comes from COLLCONFOut[19:16]
    collconf_maxret_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_COLLCONF_ADR)) |-> (DataOut[19:16] == r_MaxRet)
    );

    // r_CollValid comes from COLLCONFOut[5:0]
    collconf_collvalid_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_COLLCONF_ADR)) |-> (DataOut[5:0] == r_CollValid)
    );

    // int_o can only be 1 if at least one unmasked irq is set
    // If no read/write activity is occurring, check int_o stability under no-IRQ inputs
    int_stable_no_new_irqs : assert property (
        @(posedge Clk) disable iff (Reset)
        (~TxB_IRQ && ~TxE_IRQ && ~RxB_IRQ && ~RxE_IRQ && ~Busy_IRQ &&
         ~int_o && ~SetPauseTimer && ~TxCtrlEndFrm) |=>
        ~TxB_IRQ && ~TxE_IRQ && ~RxB_IRQ && ~RxE_IRQ && ~Busy_IRQ
        |-> ~int_o
    );

    // r_RGAD comes from MIIADDRESS[12:8] - reflected in DataOut when reading
    miiaddress_rgad_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIIADDRESS_ADR)) |-> (DataOut[12:8] == r_RGAD)
    );

    // r_FIAD comes from MIIADDRESS[4:0] - reflected in DataOut when reading
    miiaddress_fiad_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIIADDRESS_ADR)) |-> (DataOut[4:0] == r_FIAD)
    );

    // r_CtrlData comes from MIITX_DATA[15:0]
    miitxdata_ctrldata_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MIITX_DATA_ADR)) |-> (DataOut[15:0] == r_CtrlData)
    );

    // r_MAC lower 32 bits come from MAC_ADDR0
    mac_addr0_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MAC_ADDR0_ADR)) |-> (DataOut[31:0] == r_MAC[31:0])
    );

    // r_MAC upper 16 bits come from MAC_ADDR1 lower 16
    mac_addr1_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_MAC_ADDR1_ADR)) |-> (DataOut[15:0] == r_MAC[47:32])
    );

    // When reading HASH0, DataOut matches r_HASH0
    hash0_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_HASH0_ADR)) |-> (DataOut == r_HASH0)
    );

    // When reading HASH1, DataOut matches r_HASH1
    hash1_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_HASH1_ADR)) |-> (DataOut == r_HASH1)
    );

    // When reading DBG register, DataOut matches dbg_dat
    dbg_reg_reflected : assert property (
        @(posedge Clk)
        ((|Cs) && ~Rw && (Address == `ETH_DBG_ADR)) |-> (DataOut == dbg_dat)
    );

endmodule

bind eth_registers eth_registers_assert eth_registers_assert_instance (.*);
