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

    // RESET_N must always be the logical inverse of PRESETn
    reset_n_inverse_of_presetn : assert property (
        @(posedge PCLK) i2c.RESET_N == ~PRESETn
    );

    // TX_F_FULL must always equal the internal w_full wire
    tx_f_full_equals_w_full : assert property (
        @(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
    );

    // TX FIFO cannot be simultaneously full and empty
    tx_fifo_not_full_and_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.TX_F_FULL && i2c.TX_F_EMPTY)
    );

    // RX FIFO cannot be simultaneously full and empty
    rx_fifo_not_full_and_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(i2c.RX_F_FULL && i2c.RX_F_EMPTY)
    );

    // TX FIFO read enable should not be asserted when TX FIFO is empty
    tx_rd_en_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_RD_EN |-> !i2c.TX_F_EMPTY
    );

    // TX FIFO write enable should not be asserted when TX FIFO is full
    tx_wr_en_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_WRITE_ENA |-> !i2c.TX_F_FULL
    );

    // RX FIFO write enable should not be asserted when RX FIFO is full
    rx_wr_en_not_when_full : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_WRITE_ENA |-> !i2c.RX_F_FULL
    );

    // RX FIFO read enable should not be asserted when RX FIFO is empty
    rx_rd_en_not_when_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_RD_EN |-> !i2c.RX_F_EMPTY
    );

    // APB: PENABLE can only be asserted when PSELx is also asserted
    penable_requires_pselx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // APB: PENABLE must be preceded by PSELx being asserted one cycle earlier
    pselx_before_penable : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && !PENABLE) |=> (PSELx && PENABLE)
    );

    // APB: PSLVERR should only be valid when PREADY is asserted
    pslverr_only_when_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> PREADY
    );

    // APB: Once PENABLE and PSELx are both high, PREADY must eventually be asserted
    penable_pselx_leads_to_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> ##[0:16] PREADY
    );

    // APB: PREADY should deassert after completing a transfer (one-cycle pulse or hold until done)
    pready_deasserts_after_transfer : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PREADY && PSELx && PENABLE) |=> !PENABLE
    );

    // TX and RX empty signals from module_i2c must reflect FIFO states correctly
    tx_empty_consistent_with_fifo : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_F_EMPTY |-> i2c.tx_empty
    );

    rx_empty_consistent_with_fifo : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_F_EMPTY |-> i2c.rx_empty
    );

    // TX DATA path: data written into TX FIFO should come from APB write data
    tx_data_in_driven_by_apb : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.TX_WRITE_ENA |-> (i2c.TX_DATA_IN !== 32'bx)
    );

    // RX DATA path: data written into RX FIFO should not be X when write is enabled
    rx_data_in_valid_on_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        i2c.RX_WRITE_ENA |-> (i2c.RX_DATA_IN !== 32'bx)
    );

    // REGISTER_CONFIG should be stable unless reset is applied
    register_config_stable_without_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        $stable(i2c.REGISTER_CONFIG) || !PRESETn || (PSELx && PENABLE && PWRITE)
    );

    // SDA_ENABLE and SCL_ENABLE should not both be unknown after reset
    sda_enable_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        SDA_ENABLE !== 1'bx
    );

    scl_enable_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        SCL_ENABLE !== 1'bx
    );

    // INT_RX and INT_TX should not be unknown during normal operation
    int_rx_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        INT_RX !== 1'bx
    );

    int_tx_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        INT_TX !== 1'bx
    );

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
