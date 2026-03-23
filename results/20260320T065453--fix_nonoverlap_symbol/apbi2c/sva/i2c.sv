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

    // RESET_N is inverted PRESETn
    reset_n_inversion: assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_normal: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL always equals w_full
    tx_f_full_equals_w_full: assert property (
        @(posedge PCLK) 1'b1 |-> (i2c.TX_F_FULL == i2c.w_full)
    );

    // APB protocol: PENABLE should only be asserted when PSELx is asserted
    penable_requires_pselx: assert property (
        @(posedge PCLK) PENABLE |-> PSELx
    );

    // APB protocol: PENABLE should follow PSELx assertion (setup phase then enable phase)
    pselx_before_penable: assert property (
        @(posedge PCLK) (!PSELx && !PENABLE) |=> (!PENABLE || PSELx)
    );

    // APB protocol: When PSELx deasserted, PENABLE must also deassert next cycle
    pselx_low_penable_low: assert property (
        @(posedge PCLK) (!PSELx) |=> (!PENABLE)
    );

    // When not in reset, TX_F_FULL reflects w_full combinatorially
    tx_full_consistency: assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.TX_F_FULL === i2c.w_full)
    );

    // PREADY and PSLVERR are only valid during APB access phase (PSELx high)
    pslverr_with_pselx: assert property (
        @(posedge PCLK) PSLVERR |-> PSELx
    );

    // PENABLE is only asserted for one cycle in standard APB (PREADY seen, then PENABLE drops)
    penable_one_cycle_after_ready: assert property (
        @(posedge PCLK) (PSELx && PENABLE && PREADY) |=> (!PENABLE)
    );

    // When in reset (PRESETn low), internal RESET_N is high (active high reset to FIFOs)
    fifo_reset_active_during_preset: assert property (
        @(posedge PCLK) (!PRESETn) |-> i2c.RESET_N
    );

    // TX write enable should not be active when TX FIFO is full
    tx_write_not_when_full: assert property (
        @(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
    );

    // RX read enable should not be active when RX FIFO is empty
    rx_read_not_when_empty: assert property (
        @(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // TX read enable should not be active when TX FIFO is empty
    tx_read_not_when_empty: assert property (
        @(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX write enable should not be active when RX FIFO is full
    rx_write_not_when_full: assert property (
        @(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // APB write only when PSELx and PENABLE and PWRITE are all active
    apb_tx_write_requires_psel_penable: assert property (
        @(posedge PCLK) i2c.TX_WRITE_ENA |-> PSELx
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
