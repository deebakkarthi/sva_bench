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
	output [31:0] PRDATA,
	output reg [13:0] INTERNAL_I2C_REGISTER_CONFIG,
	output reg [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
	output [31:0] WRITE_DATA_ON_TX,
	output WR_ENA,
	output RD_ENA,
	output PREADY,
	output PSLVERR,
	output INT_RX,
	output INT_TX
);

wr_ena_only_for_tx_write : assert property (WR_ENA |-> (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1));

rd_ena_only_for_rx_read : assert property (RD_ENA |-> (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1));

wr_ena_and_rd_ena_exclusive : assert property (!(WR_ENA && RD_ENA));

pslverr_reflects_error : assert property (PSLVERR == ERROR);

int_tx_reflects_tx_empty : assert property (INT_TX == TX_EMPTY);

int_rx_reflects_rx_empty : assert property (INT_RX == RX_EMPTY);

pready_only_when_valid : assert property (PREADY |-> ((WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1));

prdata_from_rx_fifo : assert property ((PADDR == 32'd4) |-> (PRDATA == READ_DATA_ON_RX));

write_data_passes_through : assert property ((PADDR == 32'd0) |-> (WRITE_DATA_ON_TX == PWDATA));

config_register_updates_at_address_8 : assert property (@(posedge PCLK) (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1 && PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

timeout_register_updates_at_address_12 : assert property (@(posedge PCLK) (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1 && PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

config_register_stable_without_write : assert property (@(posedge PCLK) disable iff (!PRESETn) (!(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

timeout_register_stable_without_write : assert property (@(posedge PCLK) disable iff (!PRESETn) (!(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)));

config_register_resets_to_zero : assert property (@(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0));

timeout_register_resets_to_zero : assert property (@(posedge PCLK) (!PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));

endmodule

bind apb apb_assert apb_assert_instance (.*);
