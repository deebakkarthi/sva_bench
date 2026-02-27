module apb_assert(
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
wr_ena_high_when_write_to_addr0 : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b1
);

wr_ena_low_when_not_write_addr0 : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b0
);

// RD_ENA assertions
rd_ena_high_when_read_from_addr4 : assert property (
    @(posedge PCLK)
    (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b1
);

rd_ena_low_when_not_read_addr4 : assert property (
    @(posedge PCLK)
    !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b0
);

// WR_ENA and RD_ENA cannot be high simultaneously
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

// PRDATA equals READ_DATA_ON_RX
prdata_equals_read_data_on_rx : assert property (
    @(posedge PCLK)
    PRDATA == READ_DATA_ON_RX
);

// WRITE_DATA_ON_TX equals PWDATA
write_data_on_tx_equals_pwdata : assert property (
    @(posedge PCLK)
    WRITE_DATA_ON_TX == PWDATA
);

// Reset behavior: INTERNAL_I2C_REGISTER_CONFIG cleared on reset
config_reg_reset : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
);

// Reset behavior: INTERNAL_I2C_REGISTER_TIMEOUT cleared on reset
timeout_reg_reset : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (apb.INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
);

// CONFIG register update on addr 8 write
config_reg_update_on_addr8_write : assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
);

// TIMEOUT register update on addr 12 write
timeout_reg_update_on_addr12_write : assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> (apb.INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
);

// CONFIG register stable when no write to addr 8
config_reg_stable_when_no_write : assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
    |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == $past(apb.INTERNAL_I2C_REGISTER_CONFIG))
);

// PREADY low when neither WR_ENA, RD_ENA, addr8, nor addr12 with PENABLE and PSELx
pready_low_when_no_valid_access : assert property (
    @(posedge PCLK)
    !(((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && (PENABLE == 1'b1 && PSELx == 1'b1)))
    |-> PREADY == 1'b0
);

endmodule

bind apb apb_assert apb_assert_instance (.*);
