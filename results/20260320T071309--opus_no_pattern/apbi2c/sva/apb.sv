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
	wr_ena_asserted: assert property (@(posedge PCLK) (PWRITE && PENABLE && PADDR == 32'd0 && PSELx) |-> WR_ENA == 1'b1);

	// WR_ENA deasserted when conditions not met
	wr_ena_deasserted_no_write: assert property (@(posedge PCLK) (!PWRITE || !PENABLE || PADDR != 32'd0 || !PSELx) |-> WR_ENA == 1'b0);

	// RD_ENA asserted when reading from address 4
	rd_ena_asserted: assert property (@(posedge PCLK) (!PWRITE && PENABLE && PADDR == 32'd4 && PSELx) |-> RD_ENA == 1'b1);

	// RD_ENA deasserted when conditions not met
	rd_ena_deasserted: assert property (@(posedge PCLK) (PWRITE || !PENABLE || PADDR != 32'd4 || !PSELx) |-> RD_ENA == 1'b0);

	// WR_ENA and RD_ENA are mutually exclusive
	wr_rd_mutual_exclusive: assert property (@(posedge PCLK) !(WR_ENA && RD_ENA));

	// PREADY asserted during valid access phase
	pready_asserted: assert property (@(posedge PCLK) (PENABLE && PSELx && (WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12)) |-> PREADY == 1'b1);

	// PREADY deasserted when not in valid access
	pready_deasserted: assert property (@(posedge PCLK) (!PENABLE || !PSELx) |-> PREADY == 1'b0);

	// PSLVERR reflects ERROR
	pslverr_equals_error: assert property (@(posedge PCLK) PSLVERR == ERROR);

	// INT_TX reflects TX_EMPTY
	int_tx_equals_tx_empty: assert property (@(posedge PCLK) INT_TX == TX_EMPTY);

	// INT_RX reflects RX_EMPTY
	int_rx_equals_rx_empty: assert property (@(posedge PCLK) INT_RX == RX_EMPTY);

	// WRITE_DATA_ON_TX reflects PWDATA
	write_data_equals_pwdata: assert property (@(posedge PCLK) WRITE_DATA_ON_TX == PWDATA);

	// PRDATA reflects READ_DATA_ON_RX
	prdata_equals_read_data: assert property (@(posedge PCLK) PRDATA == READ_DATA_ON_RX);

	// On reset, config register is 0
	reset_config_reg: assert property (@(posedge PCLK) !PRESETn |=> INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

	// On reset, timeout register is 0
	reset_timeout_reg: assert property (@(posedge PCLK) !PRESETn |=> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

	// Config register written when address is 8 with valid write
	config_reg_write: assert property (@(posedge PCLK) PRESETn && PADDR == 32'd8 && PSELx && PWRITE && PREADY |=> INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]));

	// Timeout register written when address is 12 with valid write
	timeout_reg_write: assert property (@(posedge PCLK) PRESETn && PADDR == 32'd12 && PSELx && PWRITE && PREADY |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]));

	// Config register stable when not being written to address 8
	config_reg_stable: assert property (@(posedge PCLK) PRESETn && !(PADDR == 32'd8 && PSELx && PWRITE && PREADY) && !(PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG));

	// Timeout register stable when not being written to address 12
	timeout_reg_stable_on_config_write: assert property (@(posedge PCLK) PRESETn && PADDR == 32'd8 && PSELx && PWRITE && PREADY |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT));

	// Timeout register stable when no valid write at all
	timeout_reg_stable_idle: assert property (@(posedge PCLK) PRESETn && !(PADDR == 32'd8 && PSELx && PWRITE && PREADY) && !(PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT));

	// APB protocol: PENABLE only with PSELx
	apb_penable_requires_pselx: assert property (@(posedge PCLK) PENABLE |-> PSELx);

	// PREADY requires PSELx and PENABLE
	pready_requires_sel_enable: assert property (@(posedge PCLK) PREADY |-> (PSELx && PENABLE));

	// Valid address range check: only 0, 4, 8, 12 are valid addresses for PREADY
	pready_valid_addr: assert property (@(posedge PCLK) PREADY |-> (PADDR == 32'd0 || PADDR == 32'd4 || PADDR == 32'd8 || PADDR == 32'd12));

	// No write enable without PSELx
	no_wr_ena_without_pselx: assert property (@(posedge PCLK) WR_ENA |-> PSELx);

	// No read enable without PSELx
	no_rd_ena_without_pselx: assert property (@(posedge PCLK) RD_ENA |-> PSELx);

	// WR_ENA implies PREADY
	wr_ena_implies_pready: assert property (@(posedge PCLK) WR_ENA |-> PREADY);

	// RD_ENA implies PREADY
	rd_ena_implies_pready: assert property (@(posedge PCLK) RD_ENA |-> PREADY);

endmodule

bind apb apb_assert apb_assert_instance (.*);
