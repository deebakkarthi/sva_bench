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

wr_ena_requires_correct_conditions : assert property (@(posedge PCLK) 
	WR_ENA == 1'b1 |-> (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1));

rd_ena_requires_correct_conditions : assert property (@(posedge PCLK) 
	RD_ENA == 1'b1 |-> (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1));

wr_ena_and_rd_ena_mutually_exclusive : assert property (@(posedge PCLK) 
	~(WR_ENA == 1'b1 && RD_ENA == 1'b1));

pready_requires_correct_conditions : assert property (@(posedge PCLK) 
	PREADY == 1'b1 |-> ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1));

pslverr_reflects_error_signal : assert property (@(posedge PCLK) 
	PSLVERR == ERROR);

int_tx_reflects_tx_empty_signal : assert property (@(posedge PCLK) 
	INT_TX == TX_EMPTY);

int_rx_reflects_rx_empty_signal : assert property (@(posedge PCLK) 
	INT_RX == RX_EMPTY);

write_data_on_tx_always_pwdata : assert property (@(posedge PCLK) 
	WRITE_DATA_ON_TX == PWDATA);

prdata_always_read_data_on_rx : assert property (@(posedge PCLK) 
	PRDATA == READ_DATA_ON_RX);

config_register_resets_to_zero : assert property (@(posedge PCLK) 
	!PRESETn |=> INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

timeout_register_resets_to_zero : assert property (@(posedge PCLK) 
	!PRESETn |=> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

config_register_updates_only_at_address_8 : assert property (@(posedge PCLK) 
	(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]));

timeout_register_updates_only_at_address_12 : assert property (@(posedge PCLK) 
	(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]));

config_register_holds_value_when_not_updated : assert property (@(posedge PCLK) 
	PRESETn && !((PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) || (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=> INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG));

timeout_register_holds_value_when_not_updated : assert property (@(posedge PCLK) 
	PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT));

endmodule

bind apb apb_assert apb_assert_instance (.*);
