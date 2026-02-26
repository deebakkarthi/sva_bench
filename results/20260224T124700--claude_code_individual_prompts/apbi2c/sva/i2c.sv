module i2c_sva(
    // APB ports
    input        PCLK,
    input        PRESETn,
    input [31:0] PADDR,
    input [31:0] PWDATA,
    input        PWRITE,
    input        PSELx,
    input        PENABLE,
    input        PREADY,
    input        PSLVERR,
    input        INT_RX,
    input        INT_TX,
    input [31:0] PRDATA,
    // I2C output
    input        SDA_ENABLE,
    input        SCL_ENABLE,
    inout        SDA,
    inout        SCL,
    // internal wires exposed via bind
    input        RESET_N,
    input        TX_WRITE_ENA,
    input [31:0] TX_DATA_IN,
    input        RX_RD_EN,
    input [31:0] RX_DATA_OUT,
    input        TX_F_FULL,
    input        w_full,
    input        error,
    input        tx_empty,
    input        rx_empty
);

  // -----------------------------------------------------------------------
  // RESET_N is the inverted APB reset used to drive the FIFOs
  // -----------------------------------------------------------------------
  ap_reset_n_inversion: assert property (@(posedge PCLK)
    RESET_N == !PRESETn
  );

  // -----------------------------------------------------------------------
  // TX_WRITE_ENA: write to addr 0 with PENABLE+PSELx+PWRITE
  // -----------------------------------------------------------------------
  ap_tx_write_ena_from_apb: assert property (@(posedge PCLK)
    PRESETn |->
    (TX_WRITE_ENA == (PWRITE && PENABLE && PSELx && (PADDR == 32'd0)))
  );

  // -----------------------------------------------------------------------
  // TX data input carries PWDATA through APB
  // -----------------------------------------------------------------------
  ap_tx_data_in_from_apb: assert property (@(posedge PCLK)
    PRESETn |-> (TX_DATA_IN == PWDATA)
  );

  // -----------------------------------------------------------------------
  // RX read enable: read from addr 4 with PENABLE+PSELx+!PWRITE
  // -----------------------------------------------------------------------
  ap_rx_rd_en_from_apb: assert property (@(posedge PCLK)
    PRESETn |->
    (RX_RD_EN == (!PWRITE && PENABLE && PSELx && (PADDR == 32'd4)))
  );

  // -----------------------------------------------------------------------
  // PRDATA is fed from RX FIFO data_out
  // -----------------------------------------------------------------------
  ap_prdata_from_rx_fifo: assert property (@(posedge PCLK)
    PRESETn |-> (PRDATA == RX_DATA_OUT)
  );

  // -----------------------------------------------------------------------
  // TX_F_FULL mirrors the w_full wire from DUT_FIFO_TX
  // -----------------------------------------------------------------------
  ap_tx_full_wire: assert property (@(posedge PCLK)
    TX_F_FULL == w_full
  );

  // -----------------------------------------------------------------------
  // When PRESETn is low, FIFO reset (RESET_N) must be high
  // -----------------------------------------------------------------------
  ap_fifo_reset_active_on_apb_reset: assert property (@(posedge PCLK)
    !PRESETn |-> RESET_N
  );

  // -----------------------------------------------------------------------
  // When PRESETn is high, FIFO reset (RESET_N) must be low
  // -----------------------------------------------------------------------
  ap_fifo_reset_inactive_when_apb_active: assert property (@(posedge PCLK)
    PRESETn |-> !RESET_N
  );

  // -----------------------------------------------------------------------
  // PREADY requires PSELx and PENABLE
  // -----------------------------------------------------------------------
  ap_pready_requires_sel_enable: assert property (@(posedge PCLK)
    (PRESETn && PREADY) |-> (PSELx && PENABLE)
  );

  // -----------------------------------------------------------------------
  // PSLVERR mirrors the internal error signal from module_i2c
  // -----------------------------------------------------------------------
  ap_pslverr_mirrors_error: assert property (@(posedge PCLK)
    PRESETn |-> (PSLVERR == error)
  );

  // -----------------------------------------------------------------------
  // INT_TX mirrors tx_empty
  // -----------------------------------------------------------------------
  ap_int_tx_mirrors_tx_empty: assert property (@(posedge PCLK)
    PRESETn |-> (INT_TX == tx_empty)
  );

  // -----------------------------------------------------------------------
  // INT_RX mirrors rx_empty
  // -----------------------------------------------------------------------
  ap_int_rx_mirrors_rx_empty: assert property (@(posedge PCLK)
    PRESETn |-> (INT_RX == rx_empty)
  );

  // -----------------------------------------------------------------------
  // A write to PADDR==0 with PSELx/PENABLE/PWRITE must enable TX FIFO write
  // -----------------------------------------------------------------------
  ap_apb_write_addr0_enables_tx: assert property (@(posedge PCLK)
    (PRESETn && PWRITE && PENABLE && PSELx && (PADDR == 32'd0)) |->
    TX_WRITE_ENA
  );

  // -----------------------------------------------------------------------
  // A read from PADDR==4 with PSELx/PENABLE/!PWRITE must enable RX FIFO read
  // -----------------------------------------------------------------------
  ap_apb_read_addr4_enables_rx: assert property (@(posedge PCLK)
    (PRESETn && !PWRITE && PENABLE && PSELx && (PADDR == 32'd4)) |->
    RX_RD_EN
  );

  // -----------------------------------------------------------------------
  // TX write enable only when PSELx, PENABLE, and PWRITE are all active
  // -----------------------------------------------------------------------
  ap_tx_write_ena_requires_apb_access: assert property (@(posedge PCLK)
    (PRESETn && TX_WRITE_ENA) |-> (PSELx && PENABLE && PWRITE)
  );

  // -----------------------------------------------------------------------
  // RX read enable only when PSELx, PENABLE, and !PWRITE are all active
  // -----------------------------------------------------------------------
  ap_rx_rd_en_requires_apb_access: assert property (@(posedge PCLK)
    (PRESETn && RX_RD_EN) |-> (PSELx && PENABLE && !PWRITE)
  );

  // -----------------------------------------------------------------------
  // TX write enable and RX read enable are mutually exclusive
  // -----------------------------------------------------------------------
  ap_tx_wr_rx_rd_mutex: assert property (@(posedge PCLK)
    PRESETn |-> !(TX_WRITE_ENA && RX_RD_EN)
  );

  // -----------------------------------------------------------------------
  // Cover: a full APB write transaction to TX FIFO completes
  // -----------------------------------------------------------------------
  cp_tx_write_completes: cover property (@(posedge PCLK)
    TX_WRITE_ENA && PREADY
  );

  // -----------------------------------------------------------------------
  // Cover: a full APB read transaction from RX FIFO completes
  // -----------------------------------------------------------------------
  cp_rx_read_completes: cover property (@(posedge PCLK)
    RX_RD_EN && PREADY
  );

endmodule

bind i2c i2c_sva i_i2c_sva (
    .PCLK        (PCLK),
    .PRESETn     (PRESETn),
    .PADDR       (PADDR),
    .PWDATA      (PWDATA),
    .PWRITE      (PWRITE),
    .PSELx       (PSELx),
    .PENABLE     (PENABLE),
    .PREADY      (PREADY),
    .PSLVERR     (PSLVERR),
    .INT_RX      (INT_RX),
    .INT_TX      (INT_TX),
    .PRDATA      (PRDATA),
    .SDA_ENABLE  (SDA_ENABLE),
    .SCL_ENABLE  (SCL_ENABLE),
    .SDA         (SDA),
    .SCL         (SCL),
    .RESET_N     (RESET_N),
    .TX_WRITE_ENA(TX_WRITE_ENA),
    .TX_DATA_IN  (TX_DATA_IN),
    .RX_RD_EN    (RX_RD_EN),
    .RX_DATA_OUT (RX_DATA_OUT),
    .TX_F_FULL   (TX_F_FULL),
    .w_full      (w_full),
    .error       (error),
    .tx_empty    (tx_empty),
    .rx_empty    (rx_empty)
);
