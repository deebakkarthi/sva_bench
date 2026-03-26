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

    // RESET_N is strictly the logical inverse of PRESETn
    reset_n_inverse_of_presetn : assert property (
        @(posedge PCLK) (i2c.RESET_N === ~PRESETn)
    );

    // TX_F_FULL is always equal to w_full
    tx_f_full_equals_w_full : assert property (
        @(posedge PCLK) (i2c.TX_F_FULL === i2c.w_full)
    );

    // APB protocol: PENABLE must only be asserted when PSELx is also asserted
    penable_requires_pselx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // APB protocol: PENABLE should follow one cycle after PSELx is first asserted
    penable_follows_pselx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        ($rose(PSELx) && !PENABLE) |=> (PSELx)
    );

    // APB protocol: PENABLE deasserts after PREADY is sampled high
    penable_deasserts_after_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && PREADY) |=> (!PENABLE)
    );

    // APB protocol: Once PENABLE is asserted, PADDR must remain stable
    paddr_stable_during_penable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PADDR)
    );

    // APB protocol: Once PENABLE is asserted, PWRITE must remain stable
    pwrite_stable_during_penable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PWRITE)
    );

    // APB protocol: PWDATA must remain stable during write transfer with PENABLE
    pwdata_stable_during_write_penable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
    );

    // PSLVERR must not be asserted when PREADY is not asserted
    pslverr_requires_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> (PSELx && PENABLE && PREADY)
    );

    // When PSELx is deasserted, PREADY should eventually deassert
    pready_deasserts_when_not_selected : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!PSELx) |-> (!PENABLE)
    );

    // TX FIFO: when TX_F_FULL, write enable should not be asserted on next cycle
    tx_write_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (i2c.TX_F_FULL && i2c.TX_WRITE_ENA) |=> (!i2c.TX_WRITE_ENA || i2c.TX_RD_EN)
    );

    // RX FIFO: when RX_F_FULL, write enable should not be asserted
    rx_write_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // TX FIFO: when TX_F_EMPTY, read enable should not be asserted
    tx_read_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX FIFO: when RX_F_EMPTY, read enable should not be asserted
    rx_read_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // TX full and empty are mutually exclusive
    tx_full_empty_mutually_exclusive : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_F_FULL && i2c.TX_F_EMPTY)
    );

    // RX full and empty are mutually exclusive
    rx_full_empty_mutually_exclusive : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.RX_F_FULL && i2c.RX_F_EMPTY)
    );

    // On reset (PRESETn low), RESET_N should be high (active high reset to FIFOs)
    reset_n_high_on_presetn_low : assert property (
        @(posedge PCLK)
        (!PRESETn) |-> (i2c.RESET_N === 1'b1)
    );

    // When PRESETn is asserted, RESET_N must be deasserted
    reset_n_low_on_presetn_high : assert property (
        @(posedge PCLK)
        (PRESETn) |-> (i2c.RESET_N === 1'b0)
    );

    // REGISTER_CONFIG and TIMEOUT_CONFIG must be stable when no write transaction
    config_stable_when_no_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PSELx && PENABLE && PWRITE && PREADY) |=> $stable(i2c.REGISTER_CONFIG)
    );

    // PREADY must eventually assert after PENABLE within bounded time (max 16 cycles)
    pready_eventually_asserts : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> ##[0:16] PREADY
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
