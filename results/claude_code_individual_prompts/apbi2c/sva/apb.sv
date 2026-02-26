module apb_sva(
    input        PCLK,
    input        PRESETn,
    input        PSELx,
    input        PWRITE,
    input        PENABLE,
    input [31:0] PADDR,
    input [31:0] PWDATA,

    input [31:0] READ_DATA_ON_RX,
    input        ERROR,
    input        TX_EMPTY,
    input        RX_EMPTY,

    input [31:0] PRDATA,

    input [13:0] INTERNAL_I2C_REGISTER_CONFIG,
    input [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
    input [31:0] WRITE_DATA_ON_TX,
    input        WR_ENA,
    input        RD_ENA,

    input        PREADY,
    input        PSLVERR,

    input        INT_RX,
    input        INT_TX
);

  // -----------------------------------------------------------------------
  // WR_ENA: asserted exactly when a write transfer to address 0 is active
  // -----------------------------------------------------------------------
  ap_wr_ena_condition: assert property (@(posedge PCLK)
    PRESETn |-> (WR_ENA == (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx))
  );

  // -----------------------------------------------------------------------
  // RD_ENA: asserted exactly when a read transfer from address 4 is active
  // -----------------------------------------------------------------------
  ap_rd_ena_condition: assert property (@(posedge PCLK)
    PRESETn |-> (RD_ENA == (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx))
  );

  // -----------------------------------------------------------------------
  // PREADY: asserted when an enabled, selected transfer targets a valid addr
  // -----------------------------------------------------------------------
  ap_pready_condition: assert property (@(posedge PCLK)
    PRESETn |-> (PREADY == (
      (WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) &&
      PENABLE && PSELx
    ))
  );

  // -----------------------------------------------------------------------
  // PSLVERR mirrors ERROR
  // -----------------------------------------------------------------------
  ap_pslverr_mirrors_error: assert property (@(posedge PCLK)
    PRESETn |-> (PSLVERR == ERROR)
  );

  // -----------------------------------------------------------------------
  // INT_TX mirrors TX_EMPTY
  // -----------------------------------------------------------------------
  ap_int_tx_mirrors_tx_empty: assert property (@(posedge PCLK)
    PRESETn |-> (INT_TX == TX_EMPTY)
  );

  // -----------------------------------------------------------------------
  // INT_RX mirrors RX_EMPTY
  // -----------------------------------------------------------------------
  ap_int_rx_mirrors_rx_empty: assert property (@(posedge PCLK)
    PRESETn |-> (INT_RX == RX_EMPTY)
  );

  // -----------------------------------------------------------------------
  // PRDATA always equals READ_DATA_ON_RX (combinational pass-through)
  // -----------------------------------------------------------------------
  ap_prdata_passthrough: assert property (@(posedge PCLK)
    PRESETn |-> (PRDATA == READ_DATA_ON_RX)
  );

  // -----------------------------------------------------------------------
  // WRITE_DATA_ON_TX always equals PWDATA (combinational pass-through)
  // -----------------------------------------------------------------------
  ap_write_data_passthrough: assert property (@(posedge PCLK)
    PRESETn |-> (WRITE_DATA_ON_TX == PWDATA)
  );

  // -----------------------------------------------------------------------
  // Reset: config and timeout registers cleared one cycle after reset
  // -----------------------------------------------------------------------
  ap_reset_config: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
  );

  ap_reset_timeout: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
  );

  // -----------------------------------------------------------------------
  // Config register write: captured one cycle after a valid write to addr 8
  // -----------------------------------------------------------------------
  ap_config_reg_write: assert property (@(posedge PCLK)
    (PRESETn && PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=>
    (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
  );

  // -----------------------------------------------------------------------
  // Timeout register write: captured one cycle after valid write to addr 12
  // -----------------------------------------------------------------------
  ap_timeout_reg_write: assert property (@(posedge PCLK)
    (PRESETn && PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=>
    (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
  );

  // -----------------------------------------------------------------------
  // Config register stability: holds when no config write is in progress
  // -----------------------------------------------------------------------
  ap_config_reg_stable: assert property (@(posedge PCLK)
    (PRESETn && !(PADDR == 32'd8 && PSELx && PWRITE && PREADY)) |=>
    (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
  );

  // -----------------------------------------------------------------------
  // WR_ENA requires PENABLE and PSELx
  // -----------------------------------------------------------------------
  ap_wr_ena_requires_enable: assert property (@(posedge PCLK)
    (PRESETn && WR_ENA) |-> (PENABLE && PSELx)
  );

  // -----------------------------------------------------------------------
  // RD_ENA requires PENABLE, PSELx, and ~PWRITE
  // -----------------------------------------------------------------------
  ap_rd_ena_requires_enable: assert property (@(posedge PCLK)
    (PRESETn && RD_ENA) |-> (PENABLE && PSELx && !PWRITE)
  );

  // -----------------------------------------------------------------------
  // WR_ENA and RD_ENA are mutually exclusive
  // -----------------------------------------------------------------------
  ap_wr_rd_mutex: assert property (@(posedge PCLK)
    PRESETn |-> !(WR_ENA && RD_ENA)
  );

  // -----------------------------------------------------------------------
  // PREADY requires PSELx and PENABLE
  // -----------------------------------------------------------------------
  ap_pready_requires_sel_enable: assert property (@(posedge PCLK)
    (PRESETn && PREADY) |-> (PSELx && PENABLE)
  );

endmodule

bind apb apb_sva i_apb_sva (.*);
