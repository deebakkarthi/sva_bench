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

    // RESET_N is always the inverse of PRESETn
    reset_n_inverse_of_presetn: assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_low_when_presetn_high: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL is always equal to w_full
    tx_f_full_equals_w_full: assert property (
        @(posedge PCLK) 1'b1 |-> (i2c.TX_F_FULL == i2c.w_full)
    );

    // APB Protocol: PENABLE can only be high when PSELx is high
    penable_requires_pselx: assert property (
        @(posedge PCLK) PENABLE |-> PSELx
    );

    // APB Protocol: PENABLE should be asserted the cycle after PSELx without PENABLE
    apb_setup_to_enable: assert property (
        @(posedge PCLK) (PSELx && !PENABLE) |=> (PSELx && PENABLE)
    );

    // APB Protocol: PSLVERR is only valid when PREADY is asserted
    pslverr_valid_only_with_pready: assert property (
        @(posedge PCLK) PSLVERR |-> PREADY
    );

    // APB Protocol: PREADY deasserted means transaction not complete, PENABLE should remain
    apb_penable_held_until_pready: assert property (
        @(posedge PCLK) (PSELx && PENABLE && !PREADY) |=> (PSELx && PENABLE)
    );

    // When PSELx is deasserted, PENABLE should be deasserted
    pselx_low_implies_penable_low: assert property (
        @(posedge PCLK) (!PSELx) |-> (!PENABLE)
    );

    // TX FIFO: write enable should not be asserted when TX FIFO is full
    tx_write_not_when_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
    );

    // RX FIFO: write enable should not be asserted when RX FIFO is full
    rx_write_not_when_full: assert property (
        @(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // TX FIFO: read enable should not be asserted when TX FIFO is empty
    tx_read_not_when_empty: assert property (
        @(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX FIFO: read enable should not be asserted when RX FIFO is empty
    rx_read_not_when_empty: assert property (
        @(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // When PRESETn is low (active), system should be in reset state
    presetn_low_means_reset_active: assert property (
        @(posedge PCLK) (!PRESETn) |-> (i2c.RESET_N == 1'b1)
    );

    // PWRITE should be stable during the enable phase of APB transfer
    pwrite_stable_during_enable: assert property (
        @(posedge PCLK) (PSELx && !PENABLE && PWRITE) |=> (PSELx && PENABLE && PWRITE)
    );

    pwrite_stable_during_enable_read: assert property (
        @(posedge PCLK) (PSELx && !PENABLE && !PWRITE) |=> (PSELx && PENABLE && !PWRITE)
    );

    // PADDR should be stable during the enable phase
    paddr_stable_during_enable: assert property (
        @(posedge PCLK) (PSELx && !PENABLE) |=> (PSELx && PENABLE && ($stable(PADDR)))
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
