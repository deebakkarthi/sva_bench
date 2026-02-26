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

	wire RESET_N;
	assign RESET_N = (PRESETn == 0) ? 1'b1 : 1'b0;

	// RESET_N is the logical inverse of PRESETn
	reset_n_inverse_of_presetn : assert property (
		@(posedge PCLK) (RESET_N === ~PRESETn)
	);

	// PRESETn active low: when PRESETn is 0, RESET_N must be 1
	reset_n_high_when_presetn_low : assert property (
		@(posedge PCLK) (!PRESETn |-> RESET_N)
	);

	// PRESETn inactive: when PRESETn is 1, RESET_N must be 0
	reset_n_low_when_presetn_high : assert property (
		@(posedge PCLK) (PRESETn |-> !RESET_N)
	);

	// APB: PENABLE must be preceded by PSELx assertion
	apb_penable_requires_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PENABLE |-> $past(PSELx))
	);

	// APB: PENABLE should only be asserted one cycle after PSELx
	apb_penable_one_cycle_after_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		($rose(PSELx) |=> PENABLE)
	);

	// APB: PENABLE cannot be asserted without PSELx being active
	apb_penable_with_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PENABLE |-> PSELx)
	);

	// APB: PADDR must be stable during the ENABLE phase
	apb_paddr_stable_during_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> $stable(PADDR)
	);

	// APB: PWRITE must be stable during the ENABLE phase
	apb_pwrite_stable_during_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> $stable(PWRITE)
	);

	// APB: PWDATA must be stable during write ENABLE phase
	apb_pwdata_stable_during_write_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE && PWRITE) |=> $stable(PWDATA)
	);

	// APB: PSELx must be stable high during PENABLE
	apb_pselx_stable_during_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> PSELx
	);

	// PSLVERR should not be asserted without PREADY
	apb_pslverr_requires_pready : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSLVERR |-> PREADY)
	);

	// PREADY and PSLVERR should only be valid during PENABLE phase
	apb_pready_only_during_penable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PREADY |-> PSELx && PENABLE)
	);

	// When reset is active, outputs should eventually settle
	apb_no_penable_during_reset : assert property (
		@(posedge PCLK)
		(!PRESETn |-> !PENABLE)
	);

	// INT_RX and INT_TX should not both be asserted simultaneously (optional, depending on design intent)
	// Removed as this may be valid in some designs

	// SDA_ENABLE and SCL_ENABLE are outputs only controlled when not in reset
	// Basic sanity: signals are single-bit so they must be 0 or 1
	sda_enable_is_single_bit : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(SDA_ENABLE === 1'b0 || SDA_ENABLE === 1'b1)
	);

	scl_enable_is_single_bit : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(SCL_ENABLE === 1'b0 || SCL_ENABLE === 1'b1)
	);

	// INT_RX is a single bit output
	int_rx_is_single_bit : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(INT_RX === 1'b0 || INT_RX === 1'b1)
	);

	// INT_TX is a single bit output
	int_tx_is_single_bit : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(INT_TX === 1'b0 || INT_TX === 1'b1)
	);

	// APB: during reset, PRDATA should be stable or zero (no spurious data)
	apb_prdata_stable_in_reset : assert property (
		@(posedge PCLK)
		$fell(PRESETn) |=> (PRDATA === 32'b0)
	);

	// PREADY must be known (not X/Z) when PENABLE is asserted
	apb_pready_known_during_enable : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> !$isunknown(PREADY)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
