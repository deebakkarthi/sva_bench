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

	wr_ena_asserted_when_write_to_tx: assert property (@(posedge PCLK) (PWRITE && PENABLE && PADDR == 32'd0 && PSELx) |-> WR_ENA);
	wr_ena_deasserted_when_not_write_to_tx: assert property (@(posedge PCLK) !(PWRITE && PENABLE && PADDR == 32'd0 && PSELx) |-> !WR_ENA);
	
	rd_ena_asserted_when_read_from_rx: assert property (@(posedge PCLK) (!PWRITE && PENABLE && PADDR == 32'd4 && PSELx) |-> RD_ENA);
	rd_ena_deasserted_when_not_read_from_rx: assert property (@(posedge PCLK) !(!PWRITE && PENABLE && PADDR == 32'd4 && PSELx) |-> !RD_ENA);
	
	pready_asserted_on_valid_access: assert property (@(posedge PCLK) ((WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE && PSELx) |-> PREADY);
	pready_deasserted_on_invalid_access: assert property (@(posedge PCLK) !((WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE && PSELx) |-> !PREADY);
	
	pslverr_reflects_error: assert property (@(posedge PCLK) ERROR |-> PSLVERR);
	pslverr_clear_when_no_error: assert property (@(posedge PCLK) !ERROR |-> !PSLVERR);
	
	int_tx_reflects_tx_empty: assert property (@(posedge PCLK) TX_EMPTY |-> INT_TX);
	int_tx_clear_when_tx_not_empty: assert property (@(posedge PCLK) !TX_EMPTY |-> !INT_TX);
	
	int_rx_reflects_rx_empty: assert property (@(posedge PCLK) RX_EMPTY |-> INT_RX);
	int_rx_clear_when_rx_not_empty: assert property (@(posedge PCLK) !RX_EMPTY |-> !INT_RX);
	
	config_register_resets_on_reset: assert property (@(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0));
	timeout_register_resets_on_reset: assert property (@(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));
	
	config_register_updates_on_write: assert property (@(posedge PCLK) (PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=> (INTERNAL_I2C_REGISTER_CONFIG == PWDATA[13:0]));
	timeout_register_updates_on_write: assert property (@(posedge PCLK) (PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == PWDATA[13:0]));

endmodule

bind apb apb_assert apb_assert_instance (.*);
