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

    // RESET_N is the logical inverse of PRESETn
    reset_n_inverse_of_presetn : assert property (
        @(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
    );

    reset_n_low_when_presetn_high : assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // TX_F_FULL is always equal to w_full
    tx_f_full_equals_w_full : assert property (
        @(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
    );

    // APB: PENABLE should only be asserted when PSELx is asserted
    penable_requires_pselx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // APB: PREADY should not be asserted when PENABLE is deasserted
    pready_requires_penable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PREADY |-> PENABLE
    );

    // APB: A transaction starts with PSELx high then PENABLE high the next cycle
    apb_setup_to_enable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE) |=> (PSELx && PENABLE)
    );

    // TX write enable should not be asserted when TX FIFO is full
    tx_write_ena_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.w_full |-> !i2c.TX_WRITE_ENA
    );

    // RX read enable should not be asserted when RX FIFO is empty
    rx_rd_en_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
    );

    // TX read enable should not be asserted when TX FIFO is empty
    tx_rd_en_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
    );

    // RX write enable should not be asserted when RX FIFO is full
    rx_write_ena_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
    );

    // TX_F_EMPTY and TX_F_FULL should never be simultaneously asserted
    tx_empty_and_full_mutex : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_F_EMPTY && i2c.TX_F_FULL)
    );

    // RX_F_EMPTY and RX_F_FULL should never be simultaneously asserted
    rx_empty_and_full_mutex : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.RX_F_EMPTY && i2c.RX_F_FULL)
    );

    // PSLVERR should not be asserted without a valid APB transaction
    pslverr_requires_transaction : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> (PSELx && PENABLE)
    );

    // After reset deasserted, internal RESET_N should be low
    internal_reset_deasserted_after_preset : assert property (
        @(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
    );

    // During active reset (PRESETn low), RESET_N should be high
    internal_reset_active_during_preset_low : assert property (
        @(posedge PCLK) (!PRESETn) |-> i2c.RESET_N
    );

    // APB: PADDR should remain stable during the ENABLE phase
    paddr_stable_in_enable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE) |=> $stable(PADDR)
    );

    // APB: PWRITE should remain stable during the ENABLE phase
    pwrite_stable_in_enable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE) |=> $stable(PWRITE)
    );

    // APB: PWDATA should remain stable during the ENABLE phase when writing
    pwdata_stable_in_enable_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE && PWRITE) |=> $stable(PWDATA)
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
