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

    // TX_F_FULL is directly assigned from w_full
    tx_full_assignment: assert property (
        @(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
    );

    // APB: PENABLE must only be asserted when PSELx is also asserted
    penable_requires_pselx: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // APB: PENABLE should come after PSELx (setup phase then enable phase)
    pselx_before_penable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        ($rose(PENABLE)) |-> $past(PSELx)
    );

    // APB: PREADY should only be asserted when PENABLE is asserted
    pready_requires_penable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PREADY |-> PENABLE
    );

    // APB: PSLVERR should only be asserted when PENABLE and PREADY are both asserted
    pslverr_requires_penable_and_pready: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> (PENABLE && PREADY)
    );

    // TX FIFO: cannot be both empty and full simultaneously
    tx_fifo_not_empty_and_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_F_EMPTY && i2c.TX_F_FULL)
    );

    // RX FIFO: cannot be both empty and full simultaneously
    rx_fifo_not_empty_and_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.RX_F_EMPTY && i2c.RX_F_FULL)
    );

    // TX write enable should not be active when TX FIFO is full
    tx_write_not_when_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
    );

    // RX write enable should not be active when RX FIFO is full
    rx_write_not_when_full: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // TX read enable should not be active when TX FIFO is empty
    tx_read_not_when_empty: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX read enable should not be active when RX FIFO is empty
    rx_read_not_when_empty: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // When PRESETn deasserted (active low reset), RESET_N should be asserted (active high)
    reset_active_low_to_high: assert property (
        @(posedge PCLK) (!PRESETn) |-> i2c.RESET_N
    );

    // When PRESETn is asserted (system running), TX and RX write enables should not both be active simultaneously
    tx_rx_write_not_simultaneous: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_WRITE_ENA && i2c.RX_WRITE_ENA)
    );

    // PADDR should remain stable during ENABLE phase
    paddr_stable_during_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PADDR)
    );

    // PWRITE should remain stable during ENABLE phase
    pwrite_stable_during_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PWRITE)
    );

    // PWDATA should remain stable during write ENABLE phase
    pwdata_stable_during_write_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
