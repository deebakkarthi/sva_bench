module i2c_assert (
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

	apb_penable_requires_psel : assert property (
		@(posedge PCLK) disable iff (PRESETn == 1'b0)
		(PENABLE == 1'b1) |-> (PSELx == 1'b1)
	);

	apb_pready_with_penable : assert property (
		@(posedge PCLK) disable iff (PRESETn == 1'b0)
		(PREADY == 1'b1) |-> (PENABLE == 1'b1)
	);

	apb_pslverr_during_transaction : assert property (
		@(posedge PCLK) disable iff (PRESETn == 1'b0)
		(PSLVERR == 1'b1) |-> (PSELx == 1'b1 && PENABLE == 1'b1)
	);

	i2c_sda_open_drain : assert property (
		@(posedge PCLK) disable iff (PRESETn == 1'b0)
		(SDA_ENABLE == 1'b1) |-> (SDA == 1'b0)
	);

	i2c_scl_open_drain : assert property (
		@(posedge PCLK) disable iff (PRESETn == 1'b0)
		(SCL_ENABLE == 1'b1) |-> (SCL == 1'b0)
	);

	reset_pready_low : assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (PREADY == 1'b0)
	);

	reset_pslverr_low : assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (PSLVERR == 1'b0)
	);

	reset_interrupts_low : assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (INT_RX == 1'b0 && INT_TX == 1'b0)
	);

	reset_i2c_enables_low : assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (SDA_ENABLE == 1'b0 && SCL_ENABLE == 1'b0)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
