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

wr_ena_enable : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b1));

wr_ena_disable : assert property (@(posedge PCLK) disable iff (!PRESETn)
	~(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b0));

rd_ena_enable : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b1));

rd_ena_disable : assert property (@(posedge PCLK) disable iff (!PRESETn)
	~(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b0));

pready_on_write : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(WR_ENA == 1'b1 && PENABLE == 1'b1 && PSELx == 1'b1) |-> (PREADY == 1'b1));

pready_on_read : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(RD_ENA == 1'b1 && PENABLE == 1'b1 && PSELx == 1'b1) |-> (PREADY == 1'b1));

pready_on_config : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PADDR == 32'd8 && PSELx == 1'b1 && PENABLE == 1'b1) |-> (PREADY == 1'b1));

pready_on_timeout : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PADDR == 32'd12 && PSELx == 1'b1 && PENABLE == 1'b1) |-> (PREADY == 1'b1));

pslverr_equals_error : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PSLVERR == ERROR));

int_tx_equals_tx_empty : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(INT_TX == TX_EMPTY));

int_rx_equals_rx_empty : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(INT_RX == RX_EMPTY));

write_data_equals_pwdata : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(WRITE_DATA_ON_TX == PWDATA));

prdata_equals_read_data : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PRDATA == READ_DATA_ON_RX));

config_reg_update : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

timeout_reg_update : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

config_reg_hold : assert property (@(posedge PCLK) disable iff (!PRESETn)
	~(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

timeout_reg_hold : assert property (@(posedge PCLK) disable iff (!PRESETn)
	~(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)));

endmodule

bind apb apb_assert apb_assert_instance (.*);
