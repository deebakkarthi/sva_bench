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

    // WR_ENA asserted iff all APB write conditions at addr 0 are met
    wr_ena_when_apb_write_addr0: assert property (
        @(posedge PCLK) (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx) |-> WR_ENA
    );

    wr_ena_implies_apb_write_conditions: assert property (
        @(posedge PCLK) WR_ENA |-> (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx)
    );

    no_wr_ena_without_pwrite: assert property (
        @(posedge PCLK) !PWRITE |-> !WR_ENA
    );

    no_wr_ena_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !WR_ENA
    );

    no_wr_ena_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !WR_ENA
    );

    no_wr_ena_when_addr_not_zero: assert property (
        @(posedge PCLK) (PADDR != 32'd0) |-> !WR_ENA
    );

    // RD_ENA asserted iff all APB read conditions at addr 4 are met
    rd_ena_when_apb_read_addr4: assert property (
        @(posedge PCLK) (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx) |-> RD_ENA
    );

    rd_ena_implies_apb_read_conditions: assert property (
        @(posedge PCLK) RD_ENA |-> (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx)
    );

    no_rd_ena_when_pwrite: assert property (
        @(posedge PCLK) PWRITE |-> !RD_ENA
    );

    no_rd_ena_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !RD_ENA
    );

    no_rd_ena_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !RD_ENA
    );

    no_rd_ena_when_addr_not_four: assert property (
        @(posedge PCLK) (PADDR != 32'd4) |-> !RD_ENA
    );

    // WR_ENA and RD_ENA are mutually exclusive (PWRITE can't be 0 and 1 simultaneously)
    wr_ena_and_rd_ena_mutex: assert property (
        @(posedge PCLK) WR_ENA |-> !RD_ENA
    );

    rd_ena_and_wr_ena_mutex: assert property (
        @(posedge PCLK) RD_ENA |-> !WR_ENA
    );

    // PREADY asserted when WR_ENA active with PENABLE and PSELx
    pready_when_wr_ena: assert property (
        @(posedge PCLK) (WR_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY asserted when RD_ENA active with PENABLE and PSELx
    pready_when_rd_ena: assert property (
        @(posedge PCLK) (RD_ENA && PENABLE && PSELx) |-> PREADY
    );

    // PREADY asserted when PADDR==8 with PENABLE and PSELx
    pready_when_addr8_active: assert property (
        @(posedge PCLK) ((PADDR == 32'd8) && PENABLE && PSELx) |-> PREADY
    );

    // PREADY asserted when PADDR==12 with PENABLE and PSELx
    pready_when_addr12_active: assert property (
        @(posedge PCLK) ((PADDR == 32'd12) && PENABLE && PSELx) |-> PREADY
    );

    // PREADY deasserted when no qualifying condition is met
    no_pready_without_qualifying_condition: assert property (
        @(posedge PCLK)
        !(WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) |-> !PREADY
    );

    no_pready_without_penable: assert property (
        @(posedge PCLK) !PENABLE |-> !PREADY
    );

    no_pready_without_pselx: assert property (
        @(posedge PCLK) !PSELx |-> !PREADY
    );

    // PREADY implies PSELX and PENABLE are active
    pready_implies_pselx_penable: assert property (
        @(posedge PCLK) PREADY |-> (PSELx && PENABLE)
    );

    // PSLVERR directly mirrors ERROR
    pslverr_mirrors_error: assert property (
        @(posedge PCLK) ERROR |-> PSLVERR
    );

    no_pslverr_without_error: assert property (
        @(posedge PCLK) !ERROR |-> !PSLVERR
    );

    pslverr_implies_error: assert property (
        @(posedge PCLK) PSLVERR |-> ERROR
    );

    // INT_TX directly mirrors TX_EMPTY
    int_tx_mirrors_tx_empty: assert property (
        @(posedge PCLK) TX_EMPTY |-> INT_TX
    );

    no_int_tx_without_tx_empty: assert property (
        @(posedge PCLK) !TX_EMPTY |-> !INT_TX
    );

    int_tx_implies_tx_empty: assert property (
        @(posedge PCLK) INT_TX |-> TX_EMPTY
    );

    // INT_RX directly mirrors RX_EMPTY
    int_rx_mirrors_rx_empty: assert property (
        @(posedge PCLK) RX_EMPTY |-> INT_RX
    );

    no_int_rx_without_rx_empty: assert property (
        @(posedge PCLK) !RX_EMPTY |-> !INT_RX
    );

    int_rx_implies_rx_empty: assert property (
        @(posedge PCLK) INT_RX |-> RX_EMPTY
    );

    // WRITE_DATA_ON_TX always equals PWDATA
    write_data_on_tx_always_pwdata: assert property (
        @(posedge PCLK) 1'b1 |-> (WRITE_DATA_ON_TX == PWDATA)
    );

    // PRDATA always equals READ_DATA_ON_RX
    prdata_always_read_data_on_rx: assert property (
        @(posedge PCLK) 1'b1 |-> (PRDATA == READ_DATA_ON_RX)
    );

    // WR_ENA requires PADDR == 0, so it implies PRDATA == READ_DATA_ON_RX
    wr_ena_implies_addr_zero: assert property (
        @(posedge PCLK) WR_ENA |-> (PADDR == 32'd0)
    );

    // RD_ENA implies PADDR == 4
    rd_ena_implies_addr_four: assert property (
        @(posedge PCLK) RD_ENA |-> (PADDR == 32'd4)
    );

    // Synchronous reset: INTERNAL_I2C_REGISTER_CONFIG cleared next cycle
    reset_clears_config_register: assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // Synchronous reset: INTERNAL_I2C_REGISTER_TIMEOUT cleared next cycle
    reset_clears_timeout_register: assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // Config register updated with PWDATA[13:0] on APB write to addr 8
    config_register_updated_on_addr8_write: assert property (
        @(posedge PCLK)
        (PRESETn && (PADDR == 32'd8) && PSELx && PWRITE && PREADY)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // Timeout register updated with PWDATA[13:0] on APB write to addr 12
    timeout_register_updated_on_addr12_write: assert property (
        @(posedge PCLK)
        (PRESETn && (PADDR == 32'd12) && PSELx && PWRITE && PREADY)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // Config register holds value when no write to addr 8
    config_register_stable_when_no_addr8_write: assert property (
        @(posedge PCLK)
        (PRESETn && !((PADDR == 32'd8) && PSELx && PWRITE && PREADY))
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // Timeout register holds value when no write to addr 12
    timeout_register_stable_when_no_addr12_write: assert property (
        @(posedge PCLK)
        (PRESETn && !((PADDR == 32'd12) && PSELx && PWRITE && PREADY))
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // Config register write requires PREADY to be asserted
    config_write_requires_pready: assert property (
        @(posedge PCLK)
        ((PADDR == 32'd8) && PSELx && PWRITE && !PREADY)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // Timeout register write requires PREADY to be asserted
    timeout_write_requires_pready: assert property (
        @(posedge PCLK)
        ((PADDR == 32'd12) && PSELx && PWRITE && !PREADY)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // PREADY for config/timeout write requires PSELx and PENABLE
    addr8_pready_requires_penable_pselx: assert property (
        @(posedge PCLK)
        (PADDR == 32'd8) |-> ((PENABLE && PSELx) == PREADY)
    );

    addr12_pready_requires_penable_pselx: assert property (
        @(posedge PCLK)
        (PADDR == 32'd12) |-> ((PENABLE && PSELx) == PREADY)
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
