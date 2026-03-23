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

    // WR_ENA asserted when PWRITE=1, PENABLE=1, PADDR=0, PSELx=1
    wr_ena_asserted_on_correct_conditions: assert property (
        @(posedge PCLK) (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA
    );

    // WR_ENA deasserted when any condition not met
    wr_ena_deasserted_when_not_write: assert property (
        @(posedge PCLK) (PWRITE == 1'b0) |-> !WR_ENA
    );

    wr_ena_deasserted_when_penable_low: assert property (
        @(posedge PCLK) (PENABLE == 1'b0) |-> !WR_ENA
    );

    wr_ena_deasserted_when_paddr_not_zero: assert property (
        @(posedge PCLK) (PADDR != 32'd0) |-> !WR_ENA
    );

    wr_ena_deasserted_when_pselx_low: assert property (
        @(posedge PCLK) (PSELx == 1'b0) |-> !WR_ENA
    );

    // RD_ENA asserted when PWRITE=0, PENABLE=1, PADDR=4, PSELx=1
    rd_ena_asserted_on_correct_conditions: assert property (
        @(posedge PCLK) (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA
    );

    // RD_ENA deasserted when any condition not met
    rd_ena_deasserted_when_pwrite_high: assert property (
        @(posedge PCLK) (PWRITE == 1'b1) |-> !RD_ENA
    );

    rd_ena_deasserted_when_penable_low: assert property (
        @(posedge PCLK) (PENABLE == 1'b0) |-> !RD_ENA
    );

    rd_ena_deasserted_when_paddr_not_four: assert property (
        @(posedge PCLK) (PADDR != 32'd4) |-> !RD_ENA
    );

    rd_ena_deasserted_when_pselx_low: assert property (
        @(posedge PCLK) (PSELx == 1'b0) |-> !RD_ENA
    );

    // WR_ENA and RD_ENA are mutually exclusive (different PADDR and PWRITE requirements)
    wr_ena_rd_ena_mutually_exclusive: assert property (
        @(posedge PCLK) WR_ENA |-> !RD_ENA
    );

    // PREADY asserted when WR_ENA and PSELx and PENABLE
    pready_asserted_on_wr_ena: assert property (
        @(posedge PCLK) (WR_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY asserted when RD_ENA and PSELx and PENABLE
    pready_asserted_on_rd_ena: assert property (
        @(posedge PCLK) (RD_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY asserted when PADDR==8, PENABLE=1, PSELx=1
    pready_asserted_on_config_addr: assert property (
        @(posedge PCLK) (PADDR == 32'd8 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY
    );

    // PREADY asserted when PADDR==12, PENABLE=1, PSELx=1
    pready_asserted_on_timeout_addr: assert property (
        @(posedge PCLK) (PADDR == 32'd12 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY
    );

    // PREADY deasserted when PSELx is low
    pready_deasserted_when_pselx_low: assert property (
        @(posedge PCLK) (PSELx == 1'b0) |-> !PREADY
    );

    // PREADY deasserted when PENABLE is low
    pready_deasserted_when_penable_low: assert property (
        @(posedge PCLK) (PENABLE == 1'b0) |-> !PREADY
    );

    // PREADY deasserted when none of the enabling conditions are met
    pready_deasserted_when_no_valid_access: assert property (
        @(posedge PCLK) (!WR_ENA && !RD_ENA && PADDR != 32'd8 && PADDR != 32'd12) |-> !PREADY
    );

    // WRITE_DATA_ON_TX always equals PWDATA
    write_data_on_tx_equals_pwdata: assert property (
        @(posedge PCLK) 1'b1 |-> (WRITE_DATA_ON_TX == PWDATA)
    );

    // PRDATA always equals READ_DATA_ON_RX
    prdata_equals_read_data_on_rx: assert property (
        @(posedge PCLK) 1'b1 |-> (PRDATA == READ_DATA_ON_RX)
    );

    // PSLVERR always equals ERROR
    pslverr_equals_error: assert property (
        @(posedge PCLK) 1'b1 |-> (PSLVERR == ERROR)
    );

    // INT_TX always equals TX_EMPTY
    int_tx_equals_tx_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (INT_TX == TX_EMPTY)
    );

    // INT_RX always equals RX_EMPTY
    int_rx_equals_rx_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (INT_RX == RX_EMPTY)
    );

    // After reset: INTERNAL_I2C_REGISTER_CONFIG is 0
    reset_internal_config_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // After reset: INTERNAL_I2C_REGISTER_TIMEOUT is 0
    reset_internal_timeout_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // CONFIG register updated when PADDR=8, PSELx=1, PWRITE=1, PREADY=1
    config_register_updated_on_write: assert property (
        @(posedge PCLK) (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // TIMEOUT register updated when PADDR=12, PSELx=1, PWRITE=1, PREADY=1
    timeout_register_updated_on_write: assert property (
        @(posedge PCLK) (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // CONFIG register stable when not being written (not reset, not addr 8 write)
    config_register_stable_when_not_written: assert property (
        @(posedge PCLK) (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // TIMEOUT register stable when not being written (not reset, not addr 12 write)
    timeout_register_stable_when_not_written: assert property (
        @(posedge PCLK) (PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // WR_ENA implies PSELx, PENABLE, PWRITE are all asserted
    wr_ena_implies_pselx_penable_pwrite: assert property (
        @(posedge PCLK) WR_ENA |-> (PSELx && PENABLE && PWRITE)
    );

    // RD_ENA implies PSELx, PENABLE asserted and PWRITE deasserted
    rd_ena_implies_pselx_penable_no_pwrite: assert property (
        @(posedge PCLK) RD_ENA |-> (PSELx && PENABLE && !PWRITE)
    );

    // WR_ENA implies PREADY
    wr_ena_implies_pready: assert property (
        @(posedge PCLK) WR_ENA |-> PREADY
    );

    // RD_ENA implies PREADY
    rd_ena_implies_pready: assert property (
        @(posedge PCLK) RD_ENA |-> PREADY
    );

    // CONFIG write only occurs through PADDR=8 path
    config_only_updated_via_addr8: assert property (
        @(posedge PCLK) (PRESETn && $changed(INTERNAL_I2C_REGISTER_CONFIG)) |-> $past(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    );

    // TIMEOUT write only occurs through PADDR=12 path
    timeout_only_updated_via_addr12: assert property (
        @(posedge PCLK) (PRESETn && $changed(INTERNAL_I2C_REGISTER_TIMEOUT)) |-> $past(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
