module i2c_assert (
    input PCLK,
    input PRESETn,
    input [31:0] PADDR,
    input [31:0] PWDATA,
    input PWRITE,
    input PSELx,
    input PENABLE,
    input PREADY,
    input PSLVERR,
    input INT_RX,
    input INT_TX,
    input [31:0] PRDATA,
    input SDA_ENABLE,
    input SCL_ENABLE,
    input SDA,
    input SCL
);

    // RESET_N is active-high complement of PRESETn (active-low)
    reset_n_high_when_presetn_low: assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_low_when_presetn_high: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL always equals w_full
    tx_f_full_equals_w_full: assert property (
        @(posedge PCLK) (i2c.TX_F_FULL == i2c.w_full)
    );

    w_full_implies_tx_f_full: assert property (
        @(posedge PCLK) i2c.w_full |-> i2c.TX_F_FULL
    );

    tx_f_full_implies_w_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL |-> i2c.w_full
    );

    // APB protocol: PENABLE only asserted when PSELx is asserted
    penable_requires_pselx: assert property (
        @(posedge PCLK) PENABLE |-> PSELx
    );

    // PSLVERR should only be meaningful during an active APB transfer
    pslverr_requires_active_transfer: assert property (
        @(posedge PCLK) PSLVERR |-> (PSELx && PENABLE)
    );

    // PREADY should only be active during an active APB transfer
    pready_requires_active_transfer: assert property (
        @(posedge PCLK) PREADY |-> (PSELx && PENABLE)
    );

    // TX FIFO: write enable requires PSELx, PENABLE, and PWRITE active (APB write transaction)
    tx_write_ena_requires_apb_write: assert property (
        @(posedge PCLK) i2c.TX_WRITE_ENA |-> (PSELx && PENABLE && PWRITE)
    );

    // RX FIFO read enable requires APB read transaction (PSELx, PENABLE, ~PWRITE)
    rx_rd_en_requires_apb_read: assert property (
        @(posedge PCLK) i2c.RX_RD_EN |-> (PSELx && PENABLE && !PWRITE)
    );

    // TX FIFO: if full, no more writes should succeed
    tx_full_no_rd_en_conflict: assert property (
        @(posedge PCLK) (i2c.TX_F_FULL && i2c.TX_F_EMPTY) |-> 1'b0
    );

    // RX FIFO: full and empty cannot be simultaneously true
    rx_full_empty_mutex: assert property (
        @(posedge PCLK) (i2c.RX_F_FULL && i2c.RX_F_EMPTY) |-> 1'b0
    );

    // TX_F_EMPTY implies tx_empty signal (both track TX FIFO empty state)
    tx_f_empty_implies_tx_empty: assert property (
        @(posedge PCLK) i2c.TX_F_EMPTY |-> i2c.tx_empty
    );

    tx_empty_implies_tx_f_empty: assert property (
        @(posedge PCLK) i2c.tx_empty |-> i2c.TX_F_EMPTY
    );

    // RX_F_EMPTY implies rx_empty signal
    rx_f_empty_implies_rx_empty: assert property (
        @(posedge PCLK) i2c.RX_F_EMPTY |-> i2c.rx_empty
    );

    rx_empty_implies_rx_f_empty: assert property (
        @(posedge PCLK) i2c.rx_empty |-> i2c.RX_F_EMPTY
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
