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
    wr_ena_when_write_conditions_met: assert property (
        @(posedge PCLK) (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA
    );

    // WR_ENA deasserted when any write condition is not met
    wr_ena_only_when_write_conditions_met: assert property (
        @(posedge PCLK) WR_ENA |-> (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    );

    // RD_ENA asserted when PWRITE=0, PENABLE=1, PADDR=4, PSELx=1
    rd_ena_when_read_conditions_met: assert property (
        @(posedge PCLK) (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA
    );

    // RD_ENA deasserted when any read condition is not met
    rd_ena_only_when_read_conditions_met: assert property (
        @(posedge PCLK) RD_ENA |-> (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    );

    // WR_ENA and RD_ENA are mutually exclusive
    wr_ena_rd_ena_mutually_exclusive: assert property (
        @(posedge PCLK) WR_ENA |-> !RD_ENA
    );

    // PREADY asserted when WR_ENA is active and PENABLE and PSELx
    pready_when_wr_ena: assert property (
        @(posedge PCLK) WR_ENA && PENABLE && PSELx |-> PREADY
    );

    // PREADY asserted when RD_ENA is active and PENABLE and PSELx
    pready_when_rd_ena: assert property (
        @(posedge PCLK) RD_ENA && PENABLE && PSELx |-> PREADY
    );

    // PREADY asserted when PADDR==8, PENABLE, PSELx
    pready_when_addr_8: assert property (
        @(posedge PCLK) (PADDR == 32'd8) && PENABLE && PSELx |-> PREADY
    );

    // PREADY asserted when PADDR==12, PENABLE, PSELx
    pready_when_addr_12: assert property (
        @(posedge PCLK) (PADDR == 32'd12) && PENABLE && PSELx |-> PREADY
    );

    // PREADY only asserted when enabling conditions are true
    pready_only_when_valid_conditions: assert property (
        @(posedge PCLK) PREADY |-> PENABLE && PSELx
    );

    // PREADY implies valid address activity
    pready_implies_valid_address_activity: assert property (
        @(posedge PCLK) PREADY |-> (WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12)
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

    // WRITE_DATA_ON_TX always equals PWDATA
    write_data_on_tx_equals_pwdata: assert property (
        @(posedge PCLK) 1'b1 |-> (WRITE_DATA_ON_TX == PWDATA)
    );

    // PRDATA always equals READ_DATA_ON_RX
    prdata_equals_read_data_on_rx: assert property (
        @(posedge PCLK) 1'b1 |-> (PRDATA == READ_DATA_ON_RX)
    );

    // On reset, INTERNAL_I2C_REGISTER_CONFIG is cleared
    reset_config_register_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // On reset, INTERNAL_I2C_REGISTER_TIMEOUT is cleared
    reset_timeout_register_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // Config register captures PWDATA[13:0] when writing to address 8 with PREADY
    config_register_captures_pwdata_at_addr8: assert property (
        @(posedge PCLK) PRESETn && (PADDR == 32'd8) && PSELx && PWRITE && PREADY |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // Timeout register captures PWDATA[13:0] when writing to address 12 with PREADY
    timeout_register_captures_pwdata_at_addr12: assert property (
        @(posedge PCLK) PRESETn && (PADDR == 32'd12) && PSELx && PWRITE && PREADY |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // Config register is stable when not writing to address 8
    config_register_stable_when_not_writing_addr8: assert property (
        @(posedge PCLK) PRESETn && !(!PRESETn) && !(PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // Timeout register is stable when not writing to address 12
    timeout_register_stable_when_not_writing_addr12: assert property (
        @(posedge PCLK) PRESETn && !(PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // WR_ENA requires PSELx to be asserted
    wr_ena_requires_pselx: assert property (
        @(posedge PCLK) WR_ENA |-> PSELx
    );

    // RD_ENA requires PSELx to be asserted
    rd_ena_requires_pselx: assert property (
        @(posedge PCLK) RD_ENA |-> PSELx
    );

    // WR_ENA requires PENABLE to be asserted
    wr_ena_requires_penable: assert property (
        @(posedge PCLK) WR_ENA |-> PENABLE
    );

    // RD_ENA requires PENABLE to be asserted
    rd_ena_requires_penable: assert property (
        @(posedge PCLK) RD_ENA |-> PENABLE
    );

    // WR_ENA implies PREADY
    wr_ena_implies_pready: assert property (
        @(posedge PCLK) WR_ENA |-> PREADY
    );

    // RD_ENA implies PREADY
    rd_ena_implies_pready: assert property (
        @(posedge PCLK) RD_ENA |-> PREADY
    );

    // Config register write only happens when PSELx, PWRITE, PREADY all asserted
    config_write_requires_pselx_pwrite_pready: assert property (
        @(posedge PCLK) PRESETn && (INTERNAL_I2C_REGISTER_CONFIG != $past(INTERNAL_I2C_REGISTER_CONFIG)) |-> ($past(PADDR) == 32'd8 && $past(PSELx) && $past(PWRITE) && $past(PREADY))
    );

    // Timeout register write only happens when PSELx, PWRITE, PREADY all asserted
    timeout_write_requires_pselx_pwrite_pready: assert property (
        @(posedge PCLK) PRESETn && (INTERNAL_I2C_REGISTER_TIMEOUT != $past(INTERNAL_I2C_REGISTER_TIMEOUT)) |-> ($past(PADDR) == 32'd12 && $past(PSELx) && $past(PWRITE) && $past(PREADY))
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
