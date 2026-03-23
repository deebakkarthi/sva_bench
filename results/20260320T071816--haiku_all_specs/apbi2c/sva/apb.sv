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

wr_ena_correct_condition: assert property (@(posedge PCLK)
	WR_ENA == (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx));

rd_ena_correct_condition: assert property (@(posedge PCLK)
	RD_ENA == (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx));

wr_and_rd_mutually_exclusive: assert property (@(posedge PCLK)
	!(WR_ENA && RD_ENA));

pready_correct_condition: assert property (@(posedge PCLK)
	PREADY == (((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx)));

pready_requires_penable_and_psel: assert property (@(posedge PCLK)
	PREADY |-> (PENABLE && PSELx));

write_data_on_tx_is_pwdata: assert property (
	WRITE_DATA_ON_TX == PWDATA);

prdata_is_read_data_on_rx: assert property (
	PRDATA == READ_DATA_ON_RX);

pslverr_reflects_error: assert property (
	PSLVERR == ERROR);

int_tx_reflects_tx_empty: assert property (
	INT_TX == TX_EMPTY);

int_rx_reflects_rx_empty: assert property (
	INT_RX == RX_EMPTY);

config_register_reset: assert property (@(posedge PCLK)
	!PRESETn |-> INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

timeout_register_reset: assert property (@(posedge PCLK)
	!PRESETn |-> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

config_register_updates_on_write: assert property (@(posedge PCLK) disable iff (!PRESETn)
	((PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

timeout_register_updates_on_write: assert property (@(posedge PCLK) disable iff (!PRESETn)
	((PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

config_register_stable_when_not_writing: assert property (@(posedge PCLK) disable iff (!PRESETn)
	!((PADDR == 32'd8 && PSELx && PWRITE && PREADY)) |=> $stable(INTERNAL_I2C_REGISTER_CONFIG));

timeout_register_stable_when_not_writing: assert property (@(posedge PCLK) disable iff (!PRESETn)
	!((PADDR == 32'd12 && PSELx && PWRITE && PREADY)) |=> $stable(INTERNAL_I2C_REGISTER_TIMEOUT));

valid_addresses_only: assert property (@(posedge PCLK)
	PREADY |-> (PADDR == 32'd0 || PADDR == 32'd4 || PADDR == 32'd8 || PADDR == 32'd12));

no_write_and_read_same_cycle: assert property (@(posedge PCLK)
	!(WR_ENA && RD_ENA));

endmodule

bind apb apb_assert apb_assert_instance (.*);
