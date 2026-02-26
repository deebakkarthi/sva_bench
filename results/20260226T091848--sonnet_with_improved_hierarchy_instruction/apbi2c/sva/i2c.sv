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

	// RESET_N is active-high inverse of PRESETn
	reset_n_inversion: assert property (
		@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
	);

	reset_n_inversion_high: assert property (
		@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
	);

	// TX_F_FULL equals w_full
	tx_f_full_eq_w_full: assert property (
		@(posedge PCLK) i2c.TX_F_FULL == i2c.w_full
	);

	// APB: PENABLE should only be asserted when PSELx is asserted
	penable_requires_pselx: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// APB: PENABLE should come one cycle after PSELx assertion
	pselx_then_penable: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE)
	);

	// PREADY should be stable while PENABLE is high and PREADY is low
	pready_stable_during_wait: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE && !PREADY) |=> (PSELx && PENABLE)
	);

	// TX FIFO: when full, write enable should not cause data loss (write and full simultaneously is a hazard)
	tx_fifo_not_written_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
	);

	// RX FIFO: when full, write enable should not be asserted
	rx_fifo_not_written_when_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
	);

	// TX FIFO: read enable should not be asserted when empty
	tx_fifo_not_read_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
	);

	// RX FIFO: read enable should not be asserted when empty
	rx_fifo_not_read_when_empty: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
	);

	// FIFO cannot be both empty and full at the same time for TX
	tx_fifo_not_empty_and_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!(i2c.TX_F_EMPTY && i2c.TX_F_FULL)
	);

	// FIFO cannot be both empty and full at the same time for RX
	rx_fifo_not_empty_and_full: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!(i2c.RX_F_EMPTY && i2c.RX_F_FULL)
	);

	// When PRESETn is deasserted (active low reset), RESET_N goes high
	reset_active_low_behavior: assert property (
		@(posedge PCLK) !PRESETn |-> i2c.RESET_N
	);

	// PSLVERR should not be asserted without a valid APB transfer
	pslverr_only_during_transfer: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> (PSELx && PENABLE)
	);

	// INT_TX and INT_RX are not simultaneously driven high (optional best-practice for separate events)
	// Commenting this out as it may not be architecturally guaranteed
	// int_rx_tx_mutex: assert property (
	//     @(posedge PCLK) disable iff (!PRESETn)
	//     !(INT_RX && INT_TX)
	// );

	// After reset deasserted, RESET_N should be low (FIFOs not being reset)
	fifo_reset_released_after_preset: assert property (
		@(posedge PCLK) $rose(PRESETn) |=> (i2c.RESET_N == 1'b0)
	);

	// TX write enable and TX data should be stable when APB write occurs
	tx_write_ena_requires_pwrite: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_WRITE_ENA |-> (PWRITE && PSELx && PENABLE && PREADY)
	);

	// RX read enable only during APB read transfer
	rx_rd_en_requires_pread: assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_RD_EN |-> (!PWRITE && PSELx && PENABLE && PREADY)
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
