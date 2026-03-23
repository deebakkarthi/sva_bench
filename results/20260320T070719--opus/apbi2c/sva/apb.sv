

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

// WR_ENA asserted when writing to address 0
wr_ena_asserted: assert property (@(posedge PCLK) (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b1);

// WR_ENA deasserted when conditions not met
wr_ena_deasserted: assert property (@(posedge PCLK) !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b0);

// RD_ENA asserted when reading from address 4
rd_ena_asserted: assert property (@(posedge PCLK) (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b1);

// RD_ENA deasserted when conditions not met
rd_ena_deasserted: assert property (@(posedge PCLK) !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b0);

// PREADY asserted during valid access phase
pready_asserted: assert property (@(posedge PCLK) ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1);

// PREADY deasserted when no valid access
pready_deasserted: assert property (@(posedge PCLK) !((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b0);

// PSLVERR mirrors ERROR
pslverr_mirrors_error: assert property (@(posedge PCLK) 1'b1 |-> PSLVERR == ERROR);

// INT_TX mirrors TX_EMPTY
int_tx_mirrors_tx_empty: assert property (@(posedge PCLK) 1'b1 |-> INT_TX == TX_EMPTY);

// INT_RX mirrors RX_EMPTY
int_rx_mirrors_rx_empty: assert property (@(posedge PCLK) 1'b1 |-> INT_RX == RX_EMPTY);

// PRDATA reflects READ_DATA_ON_RX
prdata_reflects_rx_data: assert property (@(posedge PCLK) 1'b1 |-> PRDATA == READ_DATA_ON_RX);

// WRITE_DATA_ON_TX reflects PWDATA
write_data_reflects_pwdata: assert property (@(posedge PCLK) 1'b1 |-> WRITE_DATA_ON_TX == PWDATA);

// After reset, config register is zero
reset_config_reg_zero: assert property (@(posedge PCLK) !PRESETn |=> INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

// After reset, timeout register is zero
reset_timeout_reg_zero: assert property (@(posedge PCLK) !PRESETn |=> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

// Config register updated on write to address 8
config_reg_write: assert property (@(posedge PCLK) (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]));

// Timeout register updated on write to address 12
timeout_reg_write: assert property (@(posedge PCLK) (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]));

// Config register stable when not written
config_reg_stable: assert property (@(posedge PCLK) (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG));

// WR_ENA and RD_ENA are mutually exclusive
wr_rd_mutually_exclusive: assert property (@(posedge PCLK) !(WR_ENA == 1'b1 && RD_ENA == 1'b1));

// PREADY requires PENABLE and PSELx
pready_requires_enable_sel: assert property (@(posedge PCLK) PREADY |-> (PENABLE && PSELx));

// WR_ENA requires PENABLE
wr_ena_requires_penable: assert property (@(posedge PCLK) WR_ENA |-> PENABLE);

// RD_ENA requires PENABLE
rd_ena_requires_penable: assert property (@(posedge PCLK) RD_ENA |-> PENABLE);

// WR_ENA requires PSELx
wr_ena_requires_pselx: assert property (@(posedge PCLK) WR_ENA |-> PSELx);

// RD_ENA requires PSELx
rd_ena_requires_pselx: assert property (@(posedge PCLK) RD_ENA |-> PSELx);

// WR_ENA implies PWRITE is high
wr_ena_implies_pwrite: assert property (@(posedge PCLK) WR_ENA |-> PWRITE);

// RD_ENA implies PWRITE is low
rd_ena_implies_pwrite_low: assert property (@(posedge PCLK) RD_ENA |-> !PWRITE);

endmodule

bind apb apb_assert apb_assert_instance (.*);
