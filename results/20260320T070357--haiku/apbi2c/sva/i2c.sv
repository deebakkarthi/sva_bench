module i2c_assert (
	input PCLK,
	input PRESETn,
	input [31:0] PADDR,
	input [31:0] PWDATA,
	input PWRITE,
	input PSELx,
	input PENABLE,
	input PREADY,
	input PSLVERR,
	input INT_RX,
	input INT_TX,
	input [31:0] PRDATA,
	input SDA_ENABLE,
	input SCL_ENABLE,
	input SDA,
	input SCL
);

	reset_asserted: assert property (@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1));
	reset_deasserted: assert property (@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0));
	tx_fifo_full_flag: assert property (@(posedge PCLK) i2c.w_full |-> i2c.TX_F_FULL);
	tx_fifo_not_full_flag: assert property (@(posedge PCLK) !i2c.w_full |-> !i2c.TX_F_FULL);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
