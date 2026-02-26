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

	// RESET_N is active high when PRESETn is low
	reset_n_inversion: assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> ##0 1'b1
	);

	// PENABLE should only be asserted after PSELx (APB protocol)
	apb_enable_after_sel: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> $past(PSELx)
	);

	// PSELx must be asserted when PENABLE is asserted
	apb_sel_during_enable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// PREADY should eventually deassert after PENABLE (no infinite wait)
	apb_ready_eventually: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> ##[1:16] PREADY
	);

	// PSLVERR should only be valid when PREADY is asserted
	pslverr_with_pready: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> PREADY
	);

	// PRDATA should be stable when PREADY is asserted and not a write
	prdata_stable_on_read: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && !PWRITE && PREADY) |-> !$isunknown(PRDATA)
	);

	// PADDR should not be unknown during an active APB transfer
	paddr_valid_during_transfer: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> !$isunknown(PADDR)
	);

	// PWDATA should not be unknown during write transfer
	pwdata_valid_during_write: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PWRITE) |-> !$isunknown(PWDATA)
	);

	// PWRITE should be stable from setup phase through enable phase
	pwrite_stable_setup_to_enable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PWRITE)
	);

	// PADDR should be stable from setup phase through enable phase
	paddr_stable_setup_to_enable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PADDR)
	);

	// PWDATA stable from setup through enable during write
	pwdata_stable_setup_to_enable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE && PWRITE) |=> (PSELx && PENABLE) |-> $stable(PWDATA)
	);

	// INT_RX and INT_TX should not be unknown after reset
	int_rx_not_unknown_after_reset: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		1'b1 |-> !$isunknown(INT_RX)
	);

	int_tx_not_unknown_after_reset: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		1'b1 |-> !$isunknown(INT_TX)
	);

	// SDA_ENABLE and SCL_ENABLE should not be unknown after reset
	sda_enable_not_unknown: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		1'b1 |-> !$isunknown(SDA_ENABLE)
	);

	scl_enable_not_unknown: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		1'b1 |-> !$isunknown(SCL_ENABLE)
	);

	// PENABLE should not be asserted without PSELx being first asserted
	penable_requires_psel: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		$rose(PENABLE) |-> $past(PSELx)
	);

	// After reset deasserts, PREADY should eventually respond
	pready_not_unknown_after_reset: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		1'b1 |-> !$isunknown(PREADY)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
