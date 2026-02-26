module i2c_assert(
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

	// APB protocol: PENABLE may only be high when PSELx is high
	apb_enable_requires_select : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// APB protocol: setup phase (PSELx high, PENABLE low) must be followed by access phase (PENABLE high)
	apb_setup_to_access_phase : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> PENABLE
	);

	// APB protocol: PREADY is only valid during the access phase
	apb_pready_requires_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PREADY |-> PENABLE
	);

	// APB protocol: PSLVERR is only valid when PREADY is asserted
	apb_pslverr_requires_pready : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> PREADY
	);

	// APB protocol: when PSELx deasserts, PENABLE must be low the next cycle
	apb_deselect_clears_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!PSELx |=> !PENABLE
	);

	// APB protocol: PADDR must be stable throughout the access phase
	apb_paddr_stable_during_access : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> $stable(PADDR)
	);

	// APB protocol: PWDATA must be stable during a write access phase
	apb_pwdata_stable_during_write : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
	);

	// APB protocol: PWRITE must be stable throughout the access phase
	apb_pwrite_stable_during_access : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> $stable(PWRITE)
	);

	// Reset: PREADY must be deasserted while in reset
	reset_deasserts_pready : assert property (
		@(posedge PCLK)
		!PRESETn |-> !PREADY
	);

	// Reset: PSLVERR must be deasserted while in reset
	reset_deasserts_pslverr : assert property (
		@(posedge PCLK)
		!PRESETn |-> !PSLVERR
	);

	// PRDATA must not be unknown during a completed read transaction
	prdata_valid_on_read_completion : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PREADY && !PWRITE) |-> !$isunknown(PRDATA)
	);

	// SDA_ENABLE must never be unknown after reset
	sda_enable_never_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(SDA_ENABLE)
	);

	// SCL_ENABLE must never be unknown after reset
	scl_enable_never_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(SCL_ENABLE)
	);

	// INT_RX must never be unknown after reset
	int_rx_never_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(INT_RX)
	);

	// INT_TX must never be unknown after reset
	int_tx_never_unknown : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!$isunknown(INT_TX)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
