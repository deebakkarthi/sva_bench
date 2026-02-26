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

	// RESET_N is inverse of PRESETn
	reset_n_inverse: assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
	);

	reset_n_active_high: assert property (
		@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
	);

	// TX_F_FULL should always equal w_full
	tx_f_full_eq_w_full: assert property (
		@(posedge PCLK) i2c.TX_F_FULL === i2c.w_full
	);

	// APB protocol: PENABLE can only be high if PSELx was high the previous cycle
	apb_penable_after_pselx: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> $past(PSELx)
	);

	// APB protocol: PENABLE should deassert after PREADY
	apb_penable_deasserts_after_pready: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PREADY) |=> !PENABLE
	);

	// APB: PSELX must be asserted for PENABLE to be valid
	apb_psel_before_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// When not selected, PENABLE should not be asserted without PSELx
	apb_no_penable_without_psel: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!PSELx |-> !PENABLE
	);

	// TX DATA wires are stable during valid transfer
	tx_data_in_stable_during_write: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && PWRITE) |-> (i2c.TX_DATA_IN !== 'x)
	);

	// RX read enable should not be asserted when RX FIFO is empty
	rx_rd_not_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
	);

	// TX read enable should not be asserted when TX FIFO is empty
	tx_rd_not_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
	);

	// TX write enable should not be asserted when TX FIFO is full
	tx_wr_not_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
	);

	// RX write enable should not be asserted when RX FIFO is full
	rx_wr_not_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
	);

	// PREADY must not be asserted without PSELx and PENABLE
	pready_requires_psel_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PREADY |-> (PSELx && PENABLE)
	);

	// PSLVERR only valid when PREADY is also asserted
	pslverr_requires_pready: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> PREADY
	);

	// PADDR should remain stable during PENABLE phase
	paddr_stable_during_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PADDR)
	);

	// PWRITE should remain stable during PENABLE phase
	pwrite_stable_during_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE) |-> $stable(PWRITE)
	);

	// PWDATA stable during write transfer setup and access phase
	pwdata_stable_during_write_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE && PWRITE) |=> (PSELx && PENABLE) |-> $stable(PWDATA)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
