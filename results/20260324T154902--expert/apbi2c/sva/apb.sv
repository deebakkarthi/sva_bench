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
    // Combinational output correctness
    // -------------------------------------------------------------------------

    wr_ena_requires_pwrite_penable_paddr0_pselx : assert property (
        @(posedge PCLK)
        WR_ENA === (PWRITE & PENABLE & (PADDR == 32'd0) & PSELx)
    );

    rd_ena_requires_no_pwrite_penable_paddr4_pselx : assert property (
        @(posedge PCLK)
        RD_ENA === (!PWRITE & PENABLE & (PADDR == 32'd4) & PSELx)
    );

    pready_combinational_logic : assert property (
        @(posedge PCLK)
        PREADY === (((WR_ENA | RD_ENA | (PADDR == 32'd8) | (PADDR == 32'd12)) &
                    (PENABLE & PSELx)))
    );

    write_data_on_tx_equals_pwdata : assert property (
        @(posedge PCLK)
        WRITE_DATA_ON_TX === PWDATA
    );

    prdata_equals_read_data_on_rx : assert property (
        @(posedge PCLK)
        PRDATA === READ_DATA_ON_RX
    );

    pslverr_mirrors_error : assert property (
        @(posedge PCLK)
        PSLVERR === ERROR
    );

    int_tx_mirrors_tx_empty : assert property (
        @(posedge PCLK)
        INT_TX === TX_EMPTY
    );

    int_rx_mirrors_rx_empty : assert property (
        @(posedge PCLK)
        INT_RX === RX_EMPTY
    );

    // -------------------------------------------------------------------------
    // WR_ENA and RD_ENA are mutually exclusive
    // -------------------------------------------------------------------------

    wr_ena_and_rd_ena_mutually_exclusive : assert property (
        @(posedge PCLK)
        !(WR_ENA && RD_ENA)
    );

    // -------------------------------------------------------------------------
    // WR_ENA prerequisites
    // -------------------------------------------------------------------------

    wr_ena_requires_pselx : assert property (
        @(posedge PCLK)
        WR_ENA |-> PSELx
    );

    wr_ena_requires_penable : assert property (
        @(posedge PCLK)
        WR_ENA |-> PENABLE
    );

    wr_ena_requires_pwrite : assert property (
        @(posedge PCLK)
        WR_ENA |-> PWRITE
    );

    wr_ena_requires_paddr_zero : assert property (
        @(posedge PCLK)
        WR_ENA |-> (PADDR == 32'd0)
    );

    wr_ena_deasserted_when_paddr_nonzero : assert property (
        @(posedge PCLK)
        (PADDR != 32'd0) |-> !WR_ENA
    );

    wr_ena_deasserted_when_not_pwrite : assert property (
        @(posedge PCLK)
        !PWRITE |-> !WR_ENA
    );

    wr_ena_deasserted_when_penable_low : assert property (
        @(posedge PCLK)
        !PENABLE |-> !WR_ENA
    );

    wr_ena_deasserted_when_pselx_low : assert property (
        @(posedge PCLK)
        !PSELx |-> !WR_ENA
    );

    // -------------------------------------------------------------------------
    // RD_ENA prerequisites
    // -------------------------------------------------------------------------

    rd_ena_requires_pselx : assert property (
        @(posedge PCLK)
        RD_ENA |-> PSELx
    );

    rd_ena_requires_penable : assert property (
        @(posedge PCLK)
        RD_ENA |-> PENABLE
    );

    rd_ena_requires_no_pwrite : assert property (
        @(posedge PCLK)
        RD_ENA |-> !PWRITE
    );

    rd_ena_requires_paddr_four : assert property (
        @(posedge PCLK)
        RD_ENA |-> (PADDR == 32'd4)
    );

    rd_ena_deasserted_when_paddr_not_four : assert property (
        @(posedge PCLK)
        (PADDR != 32'd4) |-> !RD_ENA
    );

    rd_ena_deasserted_when_pwrite : assert property (
        @(posedge PCLK)
        PWRITE |-> !RD_ENA
    );

    rd_ena_deasserted_when_penable_low : assert property (
        @(posedge PCLK)
        !PENABLE |-> !RD_ENA
    );

    rd_ena_deasserted_when_pselx_low : assert property (
        @(posedge PCLK)
        !PSELx |-> !RD_ENA
    );

    // -------------------------------------------------------------------------
    // PREADY prerequisites
    // -------------------------------------------------------------------------

    pready_requires_penable : assert property (
        @(posedge PCLK)
        PREADY |-> PENABLE
    );

    pready_requires_pselx : assert property (
        @(posedge PCLK)
        PREADY |-> PSELx
    );

    pready_deasserted_when_penable_low : assert property (
        @(posedge PCLK)
        !PENABLE |-> !PREADY
    );

    pready_deasserted_when_pselx_low : assert property (
        @(posedge PCLK)
        !PSELx |-> !PREADY
    );

    pready_active_on_valid_tx_write : assert property (
        @(posedge PCLK)
        WR_ENA |-> PREADY
    );

    pready_active_on_valid_rx_read : assert property (
        @(posedge PCLK)
        RD_ENA |-> PREADY
    );

    pready_active_on_config_write : assert property (
        @(posedge PCLK)
        (PADDR == 32'd8 && PENABLE && PSELx) |-> PREADY
    );

    pready_active_on_timeout_write : assert property (
        @(posedge PCLK)
        (PADDR == 32'd12 && PENABLE && PSELx) |-> PREADY
    );

    // -------------------------------------------------------------------------
    // Reset behavior
    // -------------------------------------------------------------------------

    reset_internal_config_register_to_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG === 14'd0)
    );

    reset_internal_timeout_register_to_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT === 14'd0)
    );

    // -------------------------------------------------------------------------
    // Config register update conditions
    // -------------------------------------------------------------------------

    config_register_updated_on_paddr8_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_CONFIG === $past(PWDATA[13:0]))
    );

    timeout_register_updated_on_paddr12_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT === $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------------
    // Config register stability: holds when no write to address 8
    // -------------------------------------------------------------------------

    config_register_stable_when_no_write_to_addr8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_CONFIG === $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // -------------------------------------------------------------------------
    // Timeout register stability: holds when no write to address 12
    // -------------------------------------------------------------------------

    timeout_register_stable_when_no_write_to_addr12 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT === $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // -------------------------------------------------------------------------
    // APB protocol: PENABLE must be preceded by PSELx
    // -------------------------------------------------------------------------

    penable_only_when_pselx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // -------------------------------------------------------------------------
    // Config register within 14-bit range
    // -------------------------------------------------------------------------

    config_register_within_14bit_range : assert property (
        @(posedge PCLK)
        INTERNAL_I2C_REGISTER_CONFIG <= 14'h3FFF
    );

    timeout_register_within_14bit_range : assert property (
        @(posedge PCLK)
        INTERNAL_I2C_REGISTER_TIMEOUT <= 14'h3FFF
    );

    // -------------------------------------------------------------------------
    // PSLVERR reflects ERROR immediately
    // -------------------------------------------------------------------------

    pslverr_high_when_error_high : assert property (
        @(posedge PCLK)
        ERROR |-> PSLVERR
    );

    pslverr_low_when_error_low : assert property (
        @(posedge PCLK)
        !ERROR |-> !PSLVERR
    );

    // -------------------------------------------------------------------------
    // INT_TX reflects TX_EMPTY immediately
    // -------------------------------------------------------------------------

    int_tx_high_when_tx_empty : assert property (
        @(posedge PCLK)
        TX_EMPTY |-> INT_TX
    );

    int_tx_low_when_tx_not_empty : assert property (
        @(posedge PCLK)
        !TX_EMPTY |-> !INT_TX
    );

    // -------------------------------------------------------------------------
    // INT_RX reflects RX_EMPTY immediately
    // -------------------------------------------------------------------------

    int_rx_high_when_rx_empty : assert property (
        @(posedge PCLK)
        RX_EMPTY |-> INT_RX
    );

    int_rx_low_when_rx_not_empty : assert property (
        @(posedge PCLK)
        !RX_EMPTY |-> !INT_RX
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
