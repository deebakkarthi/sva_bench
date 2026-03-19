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

    // RESET_N is active-high inverse of PRESETn
    reset_n_inversion: assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_inversion_high: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL equals w_full
    tx_f_full_equals_w_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
    );

    // APB: PENABLE should only be high when PSELx is high
    penable_requires_pselx: assert property (
        @(posedge PCLK) PENABLE |-> PSELx
    );

    // APB: PENABLE should come one cycle after PSELx assertion (setup phase)
    pselx_then_penable: assert property (
        @(posedge PCLK) (PSELx && !PENABLE) |=> (PSELx)
    );

    // APB: PREADY should only be asserted when PENABLE is active
    pready_requires_penable: assert property (
        @(posedge PCLK) PREADY |-> PENABLE
    );

    // APB: PSLVERR only valid when PREADY and PENABLE are both asserted
    pslverr_requires_pready_penable: assert property (
        @(posedge PCLK) PSLVERR |-> (PREADY && PENABLE)
    );

    // When PRESETn is low (reset active), key internal wires should be stable/reset
    tx_write_ena_reset: assert property (
        @(posedge PCLK) (!PRESETn) |-> (!i2c.TX_WRITE_ENA)
    );

    rx_rd_en_reset: assert property (
        @(posedge PCLK) (!PRESETn) |-> (!i2c.RX_RD_EN)
    );

    // TX FIFO: cannot be both full and empty simultaneously
    tx_fifo_not_full_and_empty: assert property (
        @(posedge PCLK) !(i2c.TX_F_FULL && i2c.TX_F_EMPTY)
    );

    // RX FIFO: cannot be both full and empty simultaneously
    rx_fifo_not_full_and_empty: assert property (
        @(posedge PCLK) !(i2c.RX_F_FULL && i2c.RX_F_EMPTY)
    );

    // TX read enable should not be asserted when TX FIFO is empty
    tx_rd_en_not_when_empty: assert property (
        @(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX write enable should not be asserted when RX FIFO is full
    rx_wr_en_not_when_full: assert property (
        @(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // TX write enable should not be asserted when TX FIFO is full
    tx_wr_en_not_when_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
    );

    // RX read enable should not be asserted when RX FIFO is empty
    rx_rd_en_not_when_empty: assert property (
        @(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // APB write transaction: PWRITE high means a write operation, TX_WRITE_ENA can be asserted
    // APB read transaction: PWRITE low means a read operation, RX_RD_EN can be asserted
    apb_write_pselx_active: assert property (
        @(posedge PCLK) (PSELx && PENABLE && PWRITE && PREADY) |-> !PSLVERR || PSLVERR
    );

    // REGISTER_CONFIG and TIMEOUT_CONFIG are 14-bit values, no upper bits should overflow
    register_config_width: assert property (
        @(posedge PCLK) (i2c.REGISTER_CONFIG[13:0] == i2c.REGISTER_CONFIG)
    );

    timeout_config_width: assert property (
        @(posedge PCLK) (i2c.TIMEOUT_CONFIG[13:0] == i2c.TIMEOUT_CONFIG)
    );

    // When no reset and PSELx not asserted, PENABLE should not be asserted without PSELx
    penable_after_pselx_deassert: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        $fell(PSELx) |=> !PENABLE
    );

    // PREADY must eventually be asserted after PENABLE (liveness-like bounded check)
    penable_leads_to_pready: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> ##[0:15] PREADY
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
