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
			output  WR_ENA,
			output  RD_ENA,
			output PREADY,
			output PSLVERR,
			output INT_RX,
			output INT_TX
	   );

wr_ena_write_enable: assert property (@(posedge PCLK) 
  (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b1));

wr_ena_write_disable: assert property (@(posedge PCLK) 
  !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b0));

rd_ena_read_enable: assert property (@(posedge PCLK) 
  (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b1));

rd_ena_read_disable: assert property (@(posedge PCLK) 
  !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b0));

pready_when_enabled: assert property (@(posedge PCLK) 
  ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1) 
  |-> (PREADY == 1'b1));

pready_when_disabled: assert property (@(posedge PCLK) 
  !(((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1)) 
  |-> (PREADY == 1'b0));

write_data_always_pwdata: assert property (@(posedge PCLK) 
  (WRITE_DATA_ON_TX == PWDATA));

prdata_always_read_data: assert property (@(posedge PCLK) 
  (PRDATA == READ_DATA_ON_RX));

pslverr_mirrors_error: assert property (@(posedge PCLK) 
  (PSLVERR == ERROR));

int_tx_mirrors_tx_empty: assert property (@(posedge PCLK) 
  (INT_TX == TX_EMPTY));

int_rx_mirrors_rx_empty: assert property (@(posedge PCLK) 
  (INT_RX == RX_EMPTY));

config_register_reset: assert property (@(posedge PCLK) 
  (!PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG == 14'd0));

timeout_register_reset: assert property (@(posedge PCLK) 
  (!PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));

config_register_write: assert property (@(posedge PCLK) 
  disable iff (!PRESETn)
  (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) 
  |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG == PWDATA[13:0]));

config_register_hold: assert property (@(posedge PCLK) 
  disable iff (!PRESETn)
  !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) 
  |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

timeout_register_write: assert property (@(posedge PCLK) 
  disable iff (!PRESETn)
  (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) 
  |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT == PWDATA[13:0]));

timeout_register_hold: assert property (@(posedge PCLK) 
  disable iff (!PRESETn)
  !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) 
  |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)));

endmodule

bind apb apb_assert apb_assert_instance (.*);
