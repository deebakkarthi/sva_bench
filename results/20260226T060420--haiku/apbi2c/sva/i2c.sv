module i2c_assert (
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
	output SDA_ENABLE,
	output SCL_ENABLE,
	inout SDA,
	inout SCL
);

reset_active_check : assert property (@(posedge PCLK) (PRESETn == 1'b0) |-> ##1 PRESETn == 1'b0 or PRESETn == 1'b1);

pready_requires_transaction : assert property (@(posedge PCLK) disable iff (~PRESETn) (PREADY == 1'b1) -> (PSELx == 1'b1 && PENABLE == 1'b1));

pslverr_only_with_enable : assert property (@(posedge PCLK) disable iff (~PRESETn) (PSLVERR == 1'b1) -> (PSELx == 1'b1 && PENABLE == 1'b1));

//int_rx_pulse_property : assert property (@(posedge PCLK) disable iff (~PRESETn) (INT_RX == 1'b1) -> ##1 (INT_RX == 1'b0 || INT_RX == 1'b1));

//int_tx_pulse_property : assert property (@(posedge PCLK) disable iff (~PRESETn) (INT_TX == 1'b1) -> ##1 (INT_TX == 1'b0 || INT_TX == 1'b1));

sda_enable_stable : assert property (@(posedge PCLK) disable iff (~PRESETn) SDA_ENABLE inside {1'b0, 1'b1});

scl_enable_stable : assert property (@(posedge PCLK) disable iff (~PRESETn) SCL_ENABLE inside {1'b0, 1'b1});

pready_pslverr_exclusion : assert property (@(posedge PCLK) disable iff (~PRESETn) ~(PREADY == 1'b1 && PSLVERR == 1'b1));

prdata_valid_when_read_complete : assert property (@(posedge PCLK) disable iff (~PRESETn) (PREADY == 1'b1 && PWRITE == 1'b0) |=> PRDATA == PRDATA);

//valid_apb_transaction : assert property (@(posedge PCLK) disable iff (~PRESETn) (PSELx == 1'b1 && PENABLE == 1'b1) -> (PREADY == 1'b1 || PSLVERR == 1'b1) ##0 ##1);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
