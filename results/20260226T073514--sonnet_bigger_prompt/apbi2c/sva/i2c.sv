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

	// RESET_N is always the inverse of PRESETn
	reset_n_inverse: assert property (
		@(posedge PCLK) (i2c.RESET_N === ~PRESETn)
	);

	// TX_F_FULL is always equal to w_full
	tx_f_full_eq_w_full: assert property (
		@(posedge PCLK) (i2c.TX_F_FULL === i2c.w_full)
	);

	// APB: PENABLE must only be asserted when PSELx is also asserted
	penable_requires_pselx: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// APB: PENABLE should be deasserted when PREADY is high (transfer complete next cycle)
	penable_deasserted_after_pready: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PREADY) |=> !PENABLE
	);

	// APB: PSLVERR must only be asserted when PENABLE and PREADY are both high
	pslverr_requires_penable_pready: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> (PSELx && PENABLE && PREADY)
	);

	// APB: PADDR should be stable during the access phase
	paddr_stable_during_access: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PADDR)
	);

	// APB: PWRITE should be stable during the access phase
	pwrite_stable_during_access: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PWRITE)
	);

	// APB: PWDATA stable during write access phase
	pwdata_stable_during_write_access: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE && PWRITE) |=> (PSELx && PENABLE && PWRITE) |-> $stable(PWDATA)
	);

	// TX FIFO: when not full and write enabled, data should be written
	tx_write_ena_not_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(i2c.TX_F_FULL) |-> !(i2c.TX_WRITE_ENA)
	);

	// RX FIFO: write enable should not be asserted when full
	rx_write_ena_not_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(i2c.RX_F_FULL) |-> !(i2c.RX_WRITE_ENA)
	);

	// TX FIFO: read enable should not be asserted when empty
	tx_rd_en_not_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(i2c.TX_F_EMPTY) |-> !(i2c.TX_RD_EN)
	);

	// RX FIFO: read enable should not be asserted when empty
	rx_rd_en_not_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(i2c.RX_F_EMPTY) |-> !(i2c.RX_RD_EN)
	);

	// After reset deasserted, TX and RX FIFOs should eventually not be full
	reset_clears_tx_full: assert property (
		@(posedge PCLK)
		$rose(PRESETn) |=> !i2c.TX_F_FULL
	);

	reset_clears_rx_full: assert property (
		@(posedge PCLK)
		$rose(PRESETn) |=> !i2c.RX_F_FULL
	);

	// During reset (PRESETn low), RESET_N should be high (active high reset to FIFOs)
	reset_n_high_during_preset_low: assert property (
		@(posedge PCLK)
		(!PRESETn) |-> (i2c.RESET_N === 1'b1)
	);

	// When PRESETn is high, RESET_N should be low
	reset_n_low_when_preset_high: assert property (
		@(posedge PCLK)
		(PRESETn) |-> (i2c.RESET_N === 1'b0)
	);

	// PREADY should not be X or Z during normal operation
	pready_not_unknown: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSELx |-> !$isunknown(PREADY)
	);

	// INT_RX and INT_TX should not be simultaneously X
	int_signals_not_unknown: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!($isunknown(INT_RX) && $isunknown(INT_TX))
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
