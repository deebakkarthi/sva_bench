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

apb_pready_requires_valid_transfer : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PREADY |-> (PSELx && PENABLE))
);

apb_pslverr_requires_valid_transfer : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PSLVERR |-> (PSELx && PENABLE))
);

apb_pready_and_pslverr_mutually_exclusive : assert property (@(posedge PCLK) disable iff (!PRESETn)
	!(PREADY && PSLVERR)
);

apb_penable_requires_pselx : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(PENABLE |-> PSELx)
);

i2c_sda_enable_is_boolean : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(SDA_ENABLE == 1'b0 || SDA_ENABLE == 1'b1)
);

i2c_scl_enable_is_boolean : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(SCL_ENABLE == 1'b0 || SCL_ENABLE == 1'b1)
);

interrupt_int_rx_is_boolean : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(INT_RX == 1'b0 || INT_RX == 1'b1)
);

interrupt_int_tx_is_boolean : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(INT_TX == 1'b0 || INT_TX == 1'b1)
);

apb_pready_low_during_idle : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(!(PSELx && PENABLE) |-> !PREADY)
);

apb_pslverr_low_during_idle : assert property (@(posedge PCLK) disable iff (!PRESETn)
	(!(PSELx && PENABLE) |-> !PSLVERR)
);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
