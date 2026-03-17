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

// WR_ENA assertions
wr_ena_high_when_conditions_met : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b1
);

wr_ena_low_when_conditions_not_met : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b0
);

// RD_ENA assertions
rd_ena_high_when_conditions_met : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b1
);

rd_ena_low_when_conditions_not_met : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b0
);

// WR_ENA and RD_ENA mutually exclusive
wr_rd_ena_mutually_exclusive : assert property (
    @(posedge PCLK)
    !(WR_ENA == 1'b1 && RD_ENA == 1'b1)
);

// PREADY assertions
pready_high_when_wr_ena : assert property (
    @(posedge PCLK)
    (WR_ENA == 1'b1 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1
);

pready_high_when_rd_ena : assert property (
    @(posedge PCLK)
    (RD_ENA == 1'b1 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1
);

pready_high_when_addr8 : assert property (
    @(posedge PCLK)
    (PADDR == 32'd8 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1
);

pready_high_when_addr12 : assert property (
    @(posedge PCLK)
    (PADDR == 32'd12 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1
);

pready_low_when_no_access : assert property (
    @(posedge PCLK)
    (WR_ENA == 1'b0 && RD_ENA == 1'b0 && PADDR != 32'd8 && PADDR != 32'd12) |-> PREADY == 1'b0
);

// WRITE_DATA_ON_TX is always PWDATA
write_data_on_tx_equals_pwdata : assert property (
    @(posedge PCLK)
    WRITE_DATA_ON_TX == PWDATA
);

// PRDATA is always READ_DATA_ON_RX
prdata_equals_read_data_on_rx : assert property (
    @(posedge PCLK)
    PRDATA == READ_DATA_ON_RX
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

// Reset behavior
reset_config_register : assert property (
    @(posedge PCLK)
    !PRESETn |=> INTERNAL_I2C_REGISTER_CONFIG == 14'd0
);

reset_timeout_register : assert property (
    @(posedge PCLK)
    !PRESETn |=> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0
);

// Config register update on PADDR==8
config_register_update_on_addr8 : assert property (
    @(posedge PCLK)
    (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])
);

// Timeout register update on PADDR==12
timeout_register_update_on_addr12 : assert property (
    @(posedge PCLK)
    (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])
);

// Config register stable when not written
config_register_stable_when_not_written : assert property (
    @(posedge PCLK)
    (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
    |=> INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)
);

// Timeout register stable when not written
timeout_register_stable_when_not_written : assert property (
    @(posedge PCLK)
    (PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
    |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)
);

// PENABLE must be asserted for PREADY to be high
pready_requires_penable : assert property (
    @(posedge PCLK)
    PREADY == 1'b1 |-> PENABLE == 1'b1
);

// PREADY requires PSELx
pready_requires_pselx : assert property (
    @(posedge PCLK)
    PREADY == 1'b1 |-> PSELx == 1'b1
);

endmodule

bind apb apb_assert apb_assert_instance (.*);
