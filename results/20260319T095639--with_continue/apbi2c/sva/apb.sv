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
    // WR_ENA asserted only on write transaction to address 0
    // -------------------------------------------------------------------------
    wr_ena_conditions: assert property (
        @(posedge PCLK)
        WR_ENA == (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    );

    // -------------------------------------------------------------------------
    // RD_ENA asserted only on read transaction to address 4
    // -------------------------------------------------------------------------
    rd_ena_conditions: assert property (
        @(posedge PCLK)
        RD_ENA == (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    );

    // -------------------------------------------------------------------------
    // WR_ENA and RD_ENA are mutually exclusive
    // -------------------------------------------------------------------------
    wr_rd_ena_mutually_exclusive: assert property (
        @(posedge PCLK) !(WR_ENA && RD_ENA)
    );

    // -------------------------------------------------------------------------
    // WR_ENA requires PWRITE high
    // -------------------------------------------------------------------------
    wr_ena_requires_pwrite: assert property (
        @(posedge PCLK) WR_ENA |-> PWRITE
    );

    // -------------------------------------------------------------------------
    // RD_ENA requires PWRITE low
    // -------------------------------------------------------------------------
    rd_ena_requires_no_pwrite: assert property (
        @(posedge PCLK) RD_ENA |-> !PWRITE
    );

    // -------------------------------------------------------------------------
    // WR_ENA requires PENABLE and PSELx
    // -------------------------------------------------------------------------
    wr_ena_requires_penable_pselx: assert property (
        @(posedge PCLK) WR_ENA |-> (PENABLE && PSELx)
    );

    // -------------------------------------------------------------------------
    // RD_ENA requires PENABLE and PSELx
    // -------------------------------------------------------------------------
    rd_ena_requires_penable_pselx: assert property (
        @(posedge PCLK) RD_ENA |-> (PENABLE && PSELx)
    );

    // -------------------------------------------------------------------------
    // WR_ENA only for address 0
    // -------------------------------------------------------------------------
    wr_ena_only_addr_0: assert property (
        @(posedge PCLK) WR_ENA |-> (PADDR == 32'd0)
    );

    // -------------------------------------------------------------------------
    // RD_ENA only for address 4
    // -------------------------------------------------------------------------
    rd_ena_only_addr_4: assert property (
        @(posedge PCLK) RD_ENA |-> (PADDR == 32'd4)
    );

    // -------------------------------------------------------------------------
    // PREADY requires PENABLE and PSELx
    // -------------------------------------------------------------------------
    pready_requires_penable_pselx: assert property (
        @(posedge PCLK) PREADY |-> (PENABLE && PSELx)
    );

    // -------------------------------------------------------------------------
    // PREADY asserted when WR_ENA active
    // -------------------------------------------------------------------------
    pready_when_wr_ena: assert property (
        @(posedge PCLK) WR_ENA |-> PREADY
    );

    // -------------------------------------------------------------------------
    // PREADY asserted when RD_ENA active
    // -------------------------------------------------------------------------
    pready_when_rd_ena: assert property (
        @(posedge PCLK) RD_ENA |-> PREADY
    );

    // -------------------------------------------------------------------------
    // PREADY asserted when PADDR==8, PENABLE, PSELx
    // -------------------------------------------------------------------------
    pready_when_addr_8: assert property (
        @(posedge PCLK) (PADDR == 32'd8 && PENABLE && PSELx) |-> PREADY
    );

    // -------------------------------------------------------------------------
    // PREADY asserted when PADDR==12, PENABLE, PSELx
    // -------------------------------------------------------------------------
    pready_when_addr_12: assert property (
        @(posedge PCLK) (PADDR == 32'd12 && PENABLE && PSELx) |-> PREADY
    );

    // -------------------------------------------------------------------------
    // PREADY deasserted when PENABLE is low
    // -------------------------------------------------------------------------
    pready_deasserted_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !PREADY
    );

    // -------------------------------------------------------------------------
    // PREADY deasserted when PSELx is low
    // -------------------------------------------------------------------------
    pready_deasserted_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !PREADY
    );

    // -------------------------------------------------------------------------
    // PSLVERR reflects ERROR
    // -------------------------------------------------------------------------
    pslverr_reflects_error: assert property (
        @(posedge PCLK) PSLVERR == ERROR
    );

    // -------------------------------------------------------------------------
    // INT_TX reflects TX_EMPTY
    // -------------------------------------------------------------------------
    int_tx_reflects_tx_empty: assert property (
        @(posedge PCLK) INT_TX == TX_EMPTY
    );

    // -------------------------------------------------------------------------
    // INT_RX reflects RX_EMPTY
    // -------------------------------------------------------------------------
    int_rx_reflects_rx_empty: assert property (
        @(posedge PCLK) INT_RX == RX_EMPTY
    );

    // -------------------------------------------------------------------------
    // WRITE_DATA_ON_TX always equals PWDATA
    // -------------------------------------------------------------------------
    write_data_on_tx_equals_pwdata: assert property (
        @(posedge PCLK) WRITE_DATA_ON_TX == PWDATA
    );

    // -------------------------------------------------------------------------
    // PRDATA always reflects READ_DATA_ON_RX
    // -------------------------------------------------------------------------
    prdata_reflects_read_data_on_rx: assert property (
        @(posedge PCLK) PRDATA == READ_DATA_ON_RX
    );

    // -------------------------------------------------------------------------
    // On reset: INTERNAL_I2C_REGISTER_CONFIG cleared
    // -------------------------------------------------------------------------
    reset_clears_config_register: assert property (
        @(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // -------------------------------------------------------------------------
    // On reset: INTERNAL_I2C_REGISTER_TIMEOUT cleared
    // -------------------------------------------------------------------------
    reset_clears_timeout_register: assert property (
        @(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // -------------------------------------------------------------------------
    // Config register written when PADDR==8, PSELx, PWRITE, PREADY
    // -------------------------------------------------------------------------
    config_register_written_on_addr_8: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------------
    // Timeout register written when PADDR==12, PSELx, PWRITE, PREADY
    // -------------------------------------------------------------------------
    timeout_register_written_on_addr_12: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------------
    // Config register stable when not written to address 8
    // -------------------------------------------------------------------------
    config_register_stable_no_write: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // -------------------------------------------------------------------------
    // Timeout register stable when not written to address 12
    // -------------------------------------------------------------------------
    timeout_register_stable_no_write: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // -------------------------------------------------------------------------
    // Config register only stores lower 14 bits of PWDATA
    // -------------------------------------------------------------------------
    config_register_14bit_width: assert property (
        @(posedge PCLK) (INTERNAL_I2C_REGISTER_CONFIG[13:0] == INTERNAL_I2C_REGISTER_CONFIG)
    );

    // -------------------------------------------------------------------------
    // Timeout register only stores lower 14 bits of PWDATA
    // -------------------------------------------------------------------------
    timeout_register_14bit_width: assert property (
        @(posedge PCLK) (INTERNAL_I2C_REGISTER_TIMEOUT[13:0] == INTERNAL_I2C_REGISTER_TIMEOUT)
    );

    // -------------------------------------------------------------------------
    // WR_ENA not asserted without PSELx
    // -------------------------------------------------------------------------
    wr_ena_not_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !WR_ENA
    );

    // -------------------------------------------------------------------------
    // RD_ENA not asserted without PSELx
    // -------------------------------------------------------------------------
    rd_ena_not_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !RD_ENA
    );

    // -------------------------------------------------------------------------
    // WR_ENA not asserted without PENABLE
    // -------------------------------------------------------------------------
    wr_ena_not_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !WR_ENA
    );

    // -------------------------------------------------------------------------
    // RD_ENA not asserted without PENABLE
    // -------------------------------------------------------------------------
    rd_ena_not_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !RD_ENA
    );

    // -------------------------------------------------------------------------
    // PREADY full combinational equivalence
    // -------------------------------------------------------------------------
    pready_full_equivalence: assert property (
        @(posedge PCLK)
        PREADY == (((WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12) && (PENABLE && PSELx)))
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
