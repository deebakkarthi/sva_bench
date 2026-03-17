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

    // WR_ENA is asserted only when PWRITE=1, PENABLE=1, PADDR=0, PSELx=1
    wr_ena_assert : assert property (
        @(posedge PCLK)
        WR_ENA == (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    );

    // RD_ENA is asserted only when PWRITE=0, PENABLE=1, PADDR=4, PSELx=1
    rd_ena_assert : assert property (
        @(posedge PCLK)
        RD_ENA == (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    );

    // WR_ENA and RD_ENA are mutually exclusive
    wr_rd_mutex : assert property (
        @(posedge PCLK)
        !(WR_ENA && RD_ENA)
    );

    // PREADY requires PENABLE and PSELx
    pready_requires_penable_pselx : assert property (
        @(posedge PCLK)
        PREADY |-> (PENABLE && PSELx)
    );

    // PREADY when WR_ENA active with PENABLE and PSELx
    pready_on_wr_ena : assert property (
        @(posedge PCLK)
        (WR_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY when RD_ENA active with PENABLE and PSELx
    pready_on_rd_ena : assert property (
        @(posedge PCLK)
        (RD_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY when PADDR=8 with PENABLE and PSELx
    pready_on_addr8 : assert property (
        @(posedge PCLK)
        (PADDR == 32'd8 && PENABLE && PSELx) |-> PREADY
    );

    // PREADY when PADDR=12 with PENABLE and PSELx
    pready_on_addr12 : assert property (
        @(posedge PCLK)
        (PADDR == 32'd12 && PENABLE && PSELx) |-> PREADY
    );

    // PSLVERR equals ERROR
    pslverr_equals_error : assert property (
        @(posedge PCLK)
        PSLVERR == ERROR
    );

    // INT_TX equals TX_EMPTY
    int_tx_equals_tx_empty : assert property (
        @(posedge PCLK)
        INT_TX == TX_EMPTY
    );

    // INT_RX equals RX_EMPTY
    int_rx_equals_rx_empty : assert property (
        @(posedge PCLK)
        INT_RX == RX_EMPTY
    );

    // WRITE_DATA_ON_TX equals PWDATA
    write_data_on_tx_equals_pwdata : assert property (
        @(posedge PCLK)
        WRITE_DATA_ON_TX == PWDATA
    );

    // PRDATA equals READ_DATA_ON_RX
    prdata_equals_read_data : assert property (
        @(posedge PCLK)
        PRDATA == READ_DATA_ON_RX
    );

    // Reset clears INTERNAL_I2C_REGISTER_CONFIG
    reset_clears_config_reg : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // Reset clears INTERNAL_I2C_REGISTER_TIMEOUT
    reset_clears_timeout_reg : assert property (
        @(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // Config register updated on write to address 8
    config_reg_update_on_addr8 : assert property (
        @(posedge PCLK)
        (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // Timeout register updated on write to address 12
    timeout_reg_update_on_addr12 : assert property (
        @(posedge PCLK)
        (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // Config register holds value when no write to address 8 or reset
    config_reg_holds_when_no_write : assert property (
        @(posedge PCLK)
        (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // Timeout register holds value when no write to address 12 or reset
    timeout_reg_holds_when_no_write : assert property (
        @(posedge PCLK)
        (PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
         && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // WR_ENA only when PADDR is 0
    wr_ena_only_addr0 : assert property (
        @(posedge PCLK)
        WR_ENA |-> (PADDR == 32'd0)
    );

    // RD_ENA only when PADDR is 4
    rd_ena_only_addr4 : assert property (
        @(posedge PCLK)
        RD_ENA |-> (PADDR == 32'd4)
    );

    // WR_ENA requires PWRITE high
    wr_ena_requires_pwrite : assert property (
        @(posedge PCLK)
        WR_ENA |-> PWRITE
    );

    // RD_ENA requires PWRITE low
    rd_ena_requires_pwrite_low : assert property (
        @(posedge PCLK)
        RD_ENA |-> !PWRITE
    );

    // WR_ENA requires PSELx
    wr_ena_requires_pselx : assert property (
        @(posedge PCLK)
        WR_ENA |-> PSELx
    );

    // RD_ENA requires PSELx
    rd_ena_requires_pselx : assert property (
        @(posedge PCLK)
        RD_ENA |-> PSELx
    );

    // WR_ENA requires PENABLE
    wr_ena_requires_penable : assert property (
        @(posedge PCLK)
        WR_ENA |-> PENABLE
    );

    // RD_ENA requires PENABLE
    rd_ena_requires_penable : assert property (
        @(posedge PCLK)
        RD_ENA |-> PENABLE
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
