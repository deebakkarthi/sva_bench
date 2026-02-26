module i2c_assert(
	//APB PORTS
	input PCLK,
	input PRESETn,
	input [31:0] PADDR,
	input [31:0] PWDATA,
	input PWRITE,
	input PSELx,
	input PENABLE,
	output PREADY,
	output PSLVERR,
	output INT_RX,
	output INT_TX,
	output [31:0] PRDATA,
	//I2C OUTPUT
	output SDA_ENABLE,
	output SCL_ENABLE,
	inout SDA,
	inout SCL
);

reset_inversion_low: assert property (@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1));

reset_inversion_high: assert property (@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0));

tx_fifo_full_consistency: assert property (@(posedge PCLK) i2c.TX_F_FULL == i2c.w_full);

tx_fifo_no_write_when_full: assert property (@(posedge PCLK) (i2c.w_full == 1'b1) |-> (i2c.TX_WRITE_ENA == 1'b0));

tx_fifo_no_read_when_empty: assert property (@(posedge PCLK) (i2c.TX_F_EMPTY == 1'b1) |-> (i2c.TX_RD_EN == 1'b0));

rx_fifo_no_write_when_full: assert property (@(posedge PCLK) (i2c.RX_F_FULL == 1'b1) |-> (i2c.RX_WRITE_ENA == 1'b0));

rx_fifo_no_read_when_empty: assert property (@(posedge PCLK) (i2c.RX_F_EMPTY == 1'b1) |-> (i2c.RX_RD_EN == 1'b0));

apb_pready_requires_active_transaction: assert property (@(posedge PCLK) (PREADY == 1'b1) |-> (PSELx == 1'b1 && PENABLE == 1'b1));

apb_pslverr_requires_active_transaction: assert property (@(posedge PCLK) (PSLVERR == 1'b1) |-> (PSELx == 1'b1 && PENABLE == 1'b1));

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
