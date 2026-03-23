module apb_assert (
    input PCLK,
    input PRESETn,
    input PSELx,
    input PWRITE,
    input PENABLE,
    input [31:0] PADDR,
    input [31:0] PWDATA,
    input [31:0] READ_DATA_ON_RX,
    input ERROR,
    input TX_EMPTY,
    input RX_EMPTY,
    input [31:0] PRDATA,
    input [13:0] INTERNAL_I2C_REGISTER_CONFIG,
    input [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
    input [31:0] WRITE_DATA_ON_TX,
    input WR_ENA,
    input RD_ENA,
    input PREADY,
    input PSLVERR,
    input INT_RX,
    input INT_TX
);

    // -------------------------------------------------------------------------
    // WR_ENA combinational assignment
    // -------------------------------------------------------------------------

    wr_ena_asserted_correctly : assert property (
        @(posedge PCLK)
        (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |->
        WR_ENA
    );

    wr_ena_deasserted_correctly : assert property (
        @(posedge PCLK)
        !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |->
        !WR_ENA
    );

    // -------------------------------------------------------------------------
    // RD_ENA combinational assignment
    // -------------------------------------------------------------------------

    rd_ena_asserted_correctly : assert property (
        @(posedge PCLK)
        (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |->
        RD_ENA
    );

    rd_ena_deasserted_correctly : assert property (
        @(posedge PCLK)
        !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |->
        !RD_ENA
    );

    // -------------------------------------------------------------------------
    // WR_ENA and RD_ENA are mutually exclusive
    // -------------------------------------------------------------------------

    wr_ena_rd_ena_mutually_exclusive : assert property (
        @(posedge PCLK)
        !(WR_ENA && RD_ENA)
    );

    // -------------------------------------------------------------------------
    // PREADY combinational assignment
    // -------------------------------------------------------------------------

    pready_asserted_on_wr_ena : assert property (
        @(posedge PCLK)
        (WR_ENA && PENABLE && PSELx) |-> PREADY
    );

    pready_asserted_on_rd_ena : assert property (
        @(posedge PCLK)
        (RD_ENA && PENABLE && PSELx) |-> PREADY
    );

    pready_asserted_on_addr_8 : assert property (
        @(posedge PCLK)
        (PADDR == 32'd8 && PENABLE && PSELx) |-> PREADY
    );

    pready_asserted_on_addr_12 : assert property (
        @(posedge PCLK)
        (PADDR == 32'd12 && PENABLE && PSELx) |-> PREADY
    );

    pready_requires_penable_and_pselx : assert property (
        @(posedge PCLK)
        PREADY |-> (PENABLE && PSELx)
    );

    pready_deasserted_when_no_valid_addr : assert property (
        @(posedge PCLK)
        (!WR_ENA && !RD_ENA && PADDR != 32'd8 && PADDR != 32'd12) |->
        !PREADY
    );

    // -------------------------------------------------------------------------
    // WRITE_DATA_ON_TX always equals PWDATA
    // -------------------------------------------------------------------------

    write_data_on_tx_equals_pwdata : assert property (
        @(posedge PCLK)
        WRITE_DATA_ON_TX == PWDATA
    );

    // -------------------------------------------------------------------------
    // PRDATA always equals READ_DATA_ON_RX
    // -------------------------------------------------------------------------

    prdata_equals_read_data_on_rx : assert property (
        @(posedge PCLK)
        PRDATA == READ_DATA_ON_RX
    );

    // -------------------------------------------------------------------------
    // PSLVERR reflects ERROR
    // -------------------------------------------------------------------------

    pslverr_equals_error : assert property (
        @(posedge PCLK)
        PSLVERR == ERROR
    );

    // -------------------------------------------------------------------------
    // INT_TX reflects TX_EMPTY
    // -------------------------------------------------------------------------

    int_tx_equals_tx_empty : assert property (
        @(posedge PCLK)
        INT_TX == TX_EMPTY
    );

    // -------------------------------------------------------------------------
    // INT_RX reflects RX_EMPTY
    // -------------------------------------------------------------------------

    int_rx_equals_rx_empty : assert property (
        @(posedge PCLK)
        INT_RX == RX_EMPTY
    );

    // -------------------------------------------------------------------------
    // Reset behaviour
    // -------------------------------------------------------------------------

    reset_config_register_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    reset_timeout_register_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // -------------------------------------------------------------------------
    // Config register updated on write to PADDR==8
    // -------------------------------------------------------------------------

    config_register_updated_on_addr_8_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------------
    // Timeout register updated on write to PADDR==12
    // -------------------------------------------------------------------------

    timeout_register_updated_on_addr_12_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------------
    // Config register stable when no write to PADDR==8
    // -------------------------------------------------------------------------

    config_register_stable_when_no_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // -------------------------------------------------------------------------
    // Timeout register stable when no write to PADDR==12
    // -------------------------------------------------------------------------

    timeout_register_stable_when_no_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // -------------------------------------------------------------------------
    // PENABLE must be asserted for any transaction to generate PREADY
    // -------------------------------------------------------------------------

    no_pready_without_penable : assert property (
        @(posedge PCLK)
        !PENABLE |-> !PREADY
    );

    // -------------------------------------------------------------------------
    // PSELx must be asserted for WR_ENA or RD_ENA
    // -------------------------------------------------------------------------

    wr_ena_requires_pselx : assert property (
        @(posedge PCLK)
        WR_ENA |-> PSELx
    );

    rd_ena_requires_pselx : assert property (
        @(posedge PCLK)
        RD_ENA |-> PSELx
    );

    // -------------------------------------------------------------------------
    // WR_ENA requires PENABLE
    // -------------------------------------------------------------------------

    wr_ena_requires_penable : assert property (
        @(posedge PCLK)
        WR_ENA |-> PENABLE
    );

    // -------------------------------------------------------------------------
    // RD_ENA requires PENABLE
    // -------------------------------------------------------------------------

    rd_ena_requires_penable : assert property (
        @(posedge PCLK)
        RD_ENA |-> PENABLE
    );

    // -------------------------------------------------------------------------
    // WR_ENA only active on PADDR == 0
    // -------------------------------------------------------------------------

    wr_ena_only_at_addr_0 : assert property (
        @(posedge PCLK)
        WR_ENA |-> (PADDR == 32'd0)
    );

    // -------------------------------------------------------------------------
    // RD_ENA only active on PADDR == 4
    // -------------------------------------------------------------------------

    rd_ena_only_at_addr_4 : assert property (
        @(posedge PCLK)
        RD_ENA |-> (PADDR == 32'd4)
    );

    // -------------------------------------------------------------------------
    // WR_ENA requires PWRITE high
    // -------------------------------------------------------------------------

    wr_ena_requires_pwrite : assert property (
        @(posedge PCLK)
        WR_ENA |-> PWRITE
    );

    // -------------------------------------------------------------------------
    // RD_ENA requires PWRITE low
    // -------------------------------------------------------------------------

    rd_ena_requires_pwrite_low : assert property (
        @(posedge PCLK)
        RD_ENA |-> !PWRITE
    );

    // -------------------------------------------------------------------------
    // INTERNAL registers hold their value across cycles when reset is high
    // and no write occurs
    // -------------------------------------------------------------------------

    config_register_holds_value_at_reset_deassert : assert property (
        @(posedge PCLK)
        PRESETn |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG !== 14'bx)
    );

    timeout_register_holds_value_at_reset_deassert : assert property (
        @(posedge PCLK)
        PRESETn |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT !== 14'bx)
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
