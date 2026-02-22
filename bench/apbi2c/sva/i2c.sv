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

	// Reset polarity: PRESETn is active low, RESET_N should be active high
	reset_polarity_check : assert property (
		@(posedge PCLK)
		(PRESETn == 1'b0) |-> ##0 1'b1
	);

	// When PRESETn is asserted (active low), PREADY should eventually deassert
	pready_deassert_on_reset : assert property (
		@(posedge PCLK)
		(!PRESETn) |-> !PREADY
	);

	// PSLVERR should not be asserted when there is no active transfer
	pslverr_only_during_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(!PSELx) |-> !PSLVERR
	);

	// PENABLE should only be asserted when PSELx is asserted
	penable_requires_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// PREADY must eventually be asserted after PENABLE is asserted
	pready_response_to_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> ##[0:16] PREADY
	);

	// INT_RX and INT_TX should not both be simultaneously asserted (mutually exclusive interrupts)
	int_rx_tx_not_simultaneous : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!(INT_RX && INT_TX)
	);

	// SDA_ENABLE and SCL_ENABLE stability after reset
	sda_enable_deassert_on_reset : assert property (
		@(posedge PCLK)
		(!PRESETn) |-> !SDA_ENABLE
	);

	scl_enable_deassert_on_reset : assert property (
		@(posedge PCLK)
		(!PRESETn) |-> !SCL_ENABLE
	);

	// PRDATA should be stable (not X/Z) during a valid read transfer
	prdata_valid_during_read : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && !PWRITE && PREADY) |-> !$isunknown(PRDATA)
	);

	// PADDR should be stable during PENABLE phase
	paddr_stable_during_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		$rose(PENABLE) |-> $stable(PADDR)
	);

	// PWDATA should be stable during PENABLE write phase
	pwdata_stable_during_penable_write : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PENABLE && PWRITE) |-> $stable(PWDATA)
	);

	// PWRITE should be stable during PENABLE phase
	pwrite_stable_during_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		$rose(PENABLE) |-> $stable(PWRITE)
	);

	// PSELx should be stable when PENABLE is high
	pselx_stable_during_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> $stable(PSELx)
	);

	// PREADY should not be unknown during active transfer
	pready_not_unknown_during_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> !$isunknown(PREADY)
	);

	// PSLVERR should not be unknown during active transfer
	pslverr_not_unknown_during_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> !$isunknown(PSLVERR)
	);

	// INT_RX should not be unknown
	int_rx_not_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(INT_RX)
	);

	// INT_TX should not be unknown
	int_tx_not_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(INT_TX)
	);

	// SDA_ENABLE should not be unknown after reset
	sda_enable_not_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(SDA_ENABLE)
	);

	// SCL_ENABLE should not be unknown after reset
	scl_enable_not_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(SCL_ENABLE)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
