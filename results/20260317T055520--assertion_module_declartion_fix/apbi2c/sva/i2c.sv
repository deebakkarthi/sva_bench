module i2c_assert (
	input PCLK,
	input PRESETn,
	input [31:0] PADDR,
	input [31:0] PWDATA,
	input PWRITE,
	input PSELx,
	input PENABLE,
	input PREADY,
	input PSLVERR,
	input INT_RX,
	input INT_TX,
	input [31:0] PRDATA,
	input SDA_ENABLE,
	input SCL_ENABLE,
	input SDA,
	input SCL
);

	// RESET_N must be the logical inverse of PRESETn
	reset_n_inverse_of_presetn : assert property (
		@(posedge PCLK) (i2c.RESET_N === ~PRESETn)
	);

	// TX_F_FULL must mirror w_full at all times
	tx_f_full_mirrors_w_full : assert property (
		@(posedge PCLK) (i2c.TX_F_FULL === i2c.w_full)
	);

	// APB: PENABLE must not be asserted without PSELx first being asserted
	penable_requires_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PENABLE |-> PSELx
	);

	// APB: PENABLE should only be high one cycle after PSELx goes high
	penable_after_pselx : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> (PSELx && PENABLE)
	);

	// APB: When PSELx is deasserted, PENABLE must also be deasserted
	penable_low_when_pselx_low : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		!PSELx |-> !PENABLE
	);

	// APB: PADDR must be stable during the entire APB transfer (setup + access phase)
	paddr_stable_during_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> $stable(PADDR)
	);

	// APB: PWDATA must be stable during write transfer
	pwdata_stable_during_write_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE && PWRITE) |=> $stable(PWDATA)
	);

	// APB: PWRITE must be stable during transfer
	pwrite_stable_during_transfer : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && !PENABLE) |=> $stable(PWRITE)
	);

	// APB: PSLVERR should only be valid when PREADY is asserted
	pslverr_valid_with_pready : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		PSLVERR |-> (PSELx && PENABLE && PREADY)
	);

	// APB: PREADY must eventually be asserted after PENABLE
	pready_eventually_asserted : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		(PSELx && PENABLE) |-> ##[0:16] PREADY
	);

	// TX write enable and RX read enable are mutually driven by APB
	// TX_WRITE_ENA should only be active when PSELx and PENABLE and PWRITE
	tx_write_ena_requires_pwrite : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_WRITE_ENA |-> (PSELx && PWRITE)
	);

	// RX_RD_EN should only be active when reading
	rx_rd_en_requires_read : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_RD_EN |-> (PSELx && !PWRITE)
	);

	// When TX FIFO is full, no new write enable should be issued
	no_tx_write_when_full : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA
	);

	// When RX FIFO is full, no new write enable to RX should be issued
	no_rx_write_when_full : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA
	);

	// When TX FIFO is empty, TX read enable should not be issued
	no_tx_read_when_empty : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN
	);

	// When RX FIFO is empty, RX read enable should not be issued
	no_rx_read_when_empty : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN
	);

	// REGISTER_CONFIG and TIMEOUT_CONFIG must be stable during active I2C operation
	// When error is asserted, PSLVERR should eventually follow
	error_implies_pslverr : assert property (
		@(posedge PCLK) disable iff (!PRESETn)
		i2c.error |-> ##[0:4] PSLVERR
	);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
