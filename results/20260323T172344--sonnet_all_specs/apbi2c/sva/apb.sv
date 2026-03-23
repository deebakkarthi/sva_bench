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

    // -------------------------------------------------------------------
    // Combinational output correctness
    // -------------------------------------------------------------------

    wr_ena_correct: assert property (
        @(posedge PCLK)
        WR_ENA == (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    );

    rd_ena_correct: assert property (
        @(posedge PCLK)
        RD_ENA == (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    );

    pslverr_equals_error: assert property (
        @(posedge PCLK)
        PSLVERR == ERROR
    );

    int_tx_equals_tx_empty: assert property (
        @(posedge PCLK)
        INT_TX == TX_EMPTY
    );

    int_rx_equals_rx_empty: assert property (
        @(posedge PCLK)
        INT_RX == RX_EMPTY
    );

    write_data_on_tx_equals_pwdata: assert property (
        @(posedge PCLK)
        WRITE_DATA_ON_TX == PWDATA
    );

    prdata_equals_read_data_on_rx: assert property (
        @(posedge PCLK)
        PRDATA == READ_DATA_ON_RX
    );

    // -------------------------------------------------------------------
    // WR_ENA asserted only under correct conditions
    // -------------------------------------------------------------------

    wr_ena_requires_pwrite: assert property (
        @(posedge PCLK)
        WR_ENA |-> PWRITE
    );

    wr_ena_requires_penable: assert property (
        @(posedge PCLK)
        WR_ENA |-> PENABLE
    );

    wr_ena_requires_pselx: assert property (
        @(posedge PCLK)
        WR_ENA |-> PSELx
    );

    wr_ena_requires_addr_zero: assert property (
        @(posedge PCLK)
        WR_ENA |-> (PADDR == 32'd0)
    );

    // -------------------------------------------------------------------
    // RD_ENA asserted only under correct conditions
    // -------------------------------------------------------------------

    rd_ena_requires_no_pwrite: assert property (
        @(posedge PCLK)
        RD_ENA |-> !PWRITE
    );

    rd_ena_requires_penable: assert property (
        @(posedge PCLK)
        RD_ENA |-> PENABLE
    );

    rd_ena_requires_pselx: assert property (
        @(posedge PCLK)
        RD_ENA |-> PSELx
    );

    rd_ena_requires_addr_four: assert property (
        @(posedge PCLK)
        RD_ENA |-> (PADDR == 32'd4)
    );

    // -------------------------------------------------------------------
    // WR_ENA and RD_ENA cannot both be asserted simultaneously
    // -------------------------------------------------------------------

    wr_rd_ena_mutually_exclusive: assert property (
        @(posedge PCLK)
        !(WR_ENA && RD_ENA)
    );

    // -------------------------------------------------------------------
    // PREADY correctness
    // -------------------------------------------------------------------

    pready_when_wr_ena_active: assert property (
        @(posedge PCLK)
        (WR_ENA && PENABLE && PSELx) |-> PREADY
    );

    pready_when_rd_ena_active: assert property (
        @(posedge PCLK)
        (RD_ENA && PENABLE && PSELx) |-> PREADY
    );

    pready_when_addr8_active: assert property (
        @(posedge PCLK)
        (PADDR == 32'd8 && PENABLE && PSELx) |-> PREADY
    );

    pready_when_addr12_active: assert property (
        @(posedge PCLK)
        (PADDR == 32'd12 && PENABLE && PSELx) |-> PREADY
    );

    pready_requires_penable: assert property (
        @(posedge PCLK)
        PREADY |-> PENABLE
    );

    pready_requires_pselx: assert property (
        @(posedge PCLK)
        PREADY |-> PSELx
    );

    pready_deasserted_when_no_valid_op: assert property (
        @(posedge PCLK)
        (!WR_ENA && !RD_ENA && PADDR != 32'd8 && PADDR != 32'd12) |-> !PREADY
    );

    // -------------------------------------------------------------------
    // Reset behavior
    // -------------------------------------------------------------------

    config_register_reset_to_zero: assert property (
        @(posedge PCLK)
        $fell(PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    timeout_register_reset_to_zero: assert property (
        @(posedge PCLK)
        $fell(PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // -------------------------------------------------------------------
    // Config register write at PADDR=8
    // -------------------------------------------------------------------

    config_reg_written_on_addr8: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------
    // Timeout register write at PADDR=12
    // -------------------------------------------------------------------

    timeout_reg_written_on_addr12: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // -------------------------------------------------------------------
    // Config register holds value when not written
    // -------------------------------------------------------------------

    config_reg_stable_when_not_written: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // -------------------------------------------------------------------
    // Timeout register holds value when not written
    // -------------------------------------------------------------------

    timeout_reg_stable_when_not_written: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // -------------------------------------------------------------------
    // Config register only updated at specific address
    // -------------------------------------------------------------------

    config_reg_only_written_at_addr8: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (INTERNAL_I2C_REGISTER_CONFIG != $past(INTERNAL_I2C_REGISTER_CONFIG))
        |-> $past(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    );

    // -------------------------------------------------------------------
    // Timeout register only updated at specific address
    // -------------------------------------------------------------------

    timeout_reg_only_written_at_addr12: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (INTERNAL_I2C_REGISTER_TIMEOUT != $past(INTERNAL_I2C_REGISTER_TIMEOUT))
        |-> $past(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    );

    // -------------------------------------------------------------------
    // APB protocol: PENABLE must follow PSELx
    // -------------------------------------------------------------------

    penable_requires_pselx: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PENABLE |-> PSELx
    );

    // -------------------------------------------------------------------
    // APB protocol: PENABLE asserted the cycle after PSELx
    // -------------------------------------------------------------------

    penable_after_pselx: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        $rose(PENABLE) |-> $past(PSELx)
    );

    // -------------------------------------------------------------------
    // PADDR stable during enable phase
    // -------------------------------------------------------------------

    paddr_stable_during_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        ##1 (PSELx && PENABLE) |-> $stable(PADDR)
    );

    // -------------------------------------------------------------------
    // PWRITE stable during enable phase
    // -------------------------------------------------------------------

    pwrite_stable_during_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE) |-> $stable(PWRITE)
    );

    // -------------------------------------------------------------------
    // PWDATA stable during write enable phase
    // -------------------------------------------------------------------

    pwdata_stable_during_write_enable: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
    );

    // -------------------------------------------------------------------
    // WR_ENA deasserted when not in proper write condition
    // -------------------------------------------------------------------

    wr_ena_deasserted_when_no_write: assert property (
        @(posedge PCLK)
        !(PWRITE && PENABLE && PADDR == 32'd0 && PSELx) |-> !WR_ENA
    );

    // -------------------------------------------------------------------
    // RD_ENA deasserted when not in proper read condition
    // -------------------------------------------------------------------

    rd_ena_deasserted_when_no_read: assert property (
        @(posedge PCLK)
        !(!PWRITE && PENABLE && PADDR == 32'd4 && PSELx) |-> !RD_ENA
    );

    // -------------------------------------------------------------------
    // Config write only happens on PREADY (no write without PREADY)
    // -------------------------------------------------------------------

    config_write_requires_pready: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx && PWRITE && !PREADY)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // -------------------------------------------------------------------
    // Timeout write only happens on PREADY
    // -------------------------------------------------------------------

    timeout_write_requires_pready: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx && PWRITE && !PREADY)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
