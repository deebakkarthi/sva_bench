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
wr_ena_assert_high : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    |-> (WR_ENA == 1'b1)
);

wr_ena_assert_low : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    |-> (WR_ENA == 1'b0)
);

// RD_ENA assertions
rd_ena_assert_high : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    |-> (RD_ENA == 1'b1)
);

rd_ena_assert_low : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    |-> (RD_ENA == 1'b0)
);

// WR_ENA and RD_ENA mutually exclusive
wr_rd_ena_mutex : assert property (
    @(posedge PCLK)
    !(WR_ENA == 1'b1 && RD_ENA == 1'b1)
);

// PREADY assertions
pready_assert_high : assert property (
    @(posedge PCLK)
    ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) &&
     PENABLE == 1'b1 && PSELx == 1'b1)
    |-> (PREADY == 1'b1)
);

pready_assert_low : assert property (
    @(posedge PCLK)
    !((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) &&
      PENABLE == 1'b1 && PSELx == 1'b1)
    |-> (PREADY == 1'b0)
);

// WRITE_DATA_ON_TX always equals PWDATA
write_data_on_tx_eq_pwdata : assert property (
    @(posedge PCLK)
    (WRITE_DATA_ON_TX == PWDATA)
);

// PRDATA always equals READ_DATA_ON_RX
prdata_eq_read_data_on_rx : assert property (
    @(posedge PCLK)
    (PRDATA == READ_DATA_ON_RX)
);

// PSLVERR equals ERROR
pslverr_eq_error : assert property (
    @(posedge PCLK)
    (PSLVERR == ERROR)
);

// INT_TX equals TX_EMPTY
int_tx_eq_tx_empty : assert property (
    @(posedge PCLK)
    (INT_TX == TX_EMPTY)
);

// INT_RX equals RX_EMPTY
int_rx_eq_rx_empty : assert property (
    @(posedge PCLK)
    (INT_RX == RX_EMPTY)
);

// Reset behavior: INTERNAL_I2C_REGISTER_CONFIG resets to 0
config_reg_reset : assert property (
    @(posedge PCLK)
    (!PRESETn)
    |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
);

// Reset behavior: INTERNAL_I2C_REGISTER_TIMEOUT resets to 0
timeout_reg_reset : assert property (
    @(posedge PCLK)
    (!PRESETn)
    |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
);

// Config register written correctly on PADDR==8 transaction
config_reg_write : assert property (
    @(posedge PCLK)
    (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
);

// Timeout register written correctly on PADDR==12 transaction
timeout_reg_write : assert property (
    @(posedge PCLK)
    (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
);

// Config register holds value when no write condition met and not in reset
config_reg_hold : assert property (
    @(posedge PCLK)
    (PRESETn &&
     !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) &&
     !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
    |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
);

// Timeout register holds value when no write on addr 12 and not addr 8 write, and not in reset
timeout_reg_hold : assert property (
    @(posedge PCLK)
    (PRESETn &&
     !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
    |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
);

// PENABLE must be asserted for PREADY to be high
pready_requires_penable : assert property (
    @(posedge PCLK)
    (PREADY == 1'b1) |-> (PENABLE == 1'b1)
);

// PENABLE must be asserted for WR_ENA to be high
wr_ena_requires_penable : assert property (
    @(posedge PCLK)
    (WR_ENA == 1'b1) |-> (PENABLE == 1'b1)
);

// PENABLE must be asserted for RD_ENA to be high
rd_ena_requires_penable : assert property (
    @(posedge PCLK)
    (RD_ENA == 1'b1) |-> (PENABLE == 1'b1)
);

// PSELx must be asserted for WR_ENA to be high
wr_ena_requires_pselx : assert property (
    @(posedge PCLK)
    (WR_ENA == 1'b1) |-> (PSELx == 1'b1)
);

// PSELx must be asserted for RD_ENA to be high
rd_ena_requires_pselx : assert property (
    @(posedge PCLK)
    (RD_ENA == 1'b1) |-> (PSELx == 1'b1)
);

// WR_ENA requires PWRITE high
wr_ena_requires_pwrite : assert property (
    @(posedge PCLK)
    (WR_ENA == 1'b1) |-> (PWRITE == 1'b1)
);

// RD_ENA requires PWRITE low
rd_ena_requires_no_pwrite : assert property (
    @(posedge PCLK)
    (RD_ENA == 1'b1) |-> (PWRITE == 1'b0)
);

// INTERNAL_I2C_REGISTER_CONFIG width check - stays within 14 bits (always true by type, but check no X/Z propagation via known value bound)
config_reg_width_check : assert property (
    @(posedge PCLK)
    PRESETn |-> (INTERNAL_I2C_REGISTER_CONFIG <= 14'h3FFF)
);

// INTERNAL_I2C_REGISTER_TIMEOUT width check
timeout_reg_width_check : assert property (
    @(posedge PCLK)
    PRESETn |-> (INTERNAL_I2C_REGISTER_TIMEOUT <= 14'h3FFF)
);

endmodule

bind apb apb_assert apb_assert_instance (.*);
