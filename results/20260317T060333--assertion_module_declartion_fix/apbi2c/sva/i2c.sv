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

    // RESET_N is inverse of PRESETn
    reset_n_inverse: assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_normal: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL should equal w_full
    tx_f_full_equals_w_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
    );

    // APB: PENABLE should only be high when PSELx is high
    penable_requires_pselx: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // APB: PENABLE should come one cycle after PSELx assertion
    penable_after_pselx: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE) |=> (PSELx)
    );

    // APB: PREADY should only be driven when PENABLE and PSELx are active
    pready_requires_enable_sel: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PREADY |-> (PSELx && PENABLE)
    );

    // After reset, TX FIFO should not be full immediately
    tx_not_full_after_reset: assert property (
        @(posedge PCLK) $fell(PRESETn) |=> !i2c.TX_F_FULL
    );

    // After reset, RX FIFO should not be full immediately
    rx_not_full_after_reset: assert property (
        @(posedge PCLK) $fell(PRESETn) |=> !i2c.RX_F_FULL
    );

    // TX FIFO cannot be both empty and full at the same time
    tx_fifo_not_empty_and_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_F_EMPTY && i2c.TX_F_FULL)
    );

    // RX FIFO cannot be both empty and full at the same time
    rx_fifo_not_empty_and_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.RX_F_EMPTY && i2c.RX_F_FULL)
    );

    // TX write enable and RX write enable should not both be active simultaneously
    tx_rx_write_mutual: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_WRITE_ENA && i2c.RX_WRITE_ENA)
    );

    // TX read enable should not be asserted when TX FIFO is empty
    tx_rd_en_not_when_empty: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX read enable should not be asserted when RX FIFO is empty
    rx_rd_en_not_when_empty: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // TX write enable should not be asserted when TX FIFO is full
    tx_wr_en_not_when_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
    );

    // RX write enable should not be asserted when RX FIFO is full
    rx_wr_en_not_when_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // PSLVERR should not be asserted without a valid APB transfer
    pslverr_requires_transfer: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> (PSELx && PENABLE)
    );

    // PRDATA should be stable while PENABLE is high and PWRITE is low
    prdata_stable_during_read: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && !PWRITE && !PREADY) |=> $stable(PRDATA)
    );

    // PADDR should remain stable during an APB transfer
    paddr_stable_during_transfer: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PADDR)
    );

    // PWDATA should remain stable during a write transfer
    pwdata_stable_during_write: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
    );

    // PWRITE should remain stable during an APB transfer
    pwrite_stable_during_transfer: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PWRITE)
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
