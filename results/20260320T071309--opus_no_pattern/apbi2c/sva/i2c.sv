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

	// RESET_N is active high reset (inverted PRESETn)
	reset_n_logic: assert property (@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1));
	reset_n_logic_inv: assert property (@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0));

	// TX_F_FULL should always equal w_full
	tx_full_assign: assert property (@(posedge PCLK) i2c.TX_F_FULL == i2c.w_full);

	// APB protocol: PENABLE should only be asserted when PSELx is asserted
	apb_penable_requires_pselx: assert property (@(posedge PCLK) PENABLE |-> PSELx);

	// APB protocol: PREADY should not be asserted when PSELx is low
	apb_pready_requires_pselx: assert property (@(posedge PCLK) PREADY |-> PSELx);

	// APB protocol: PSLVERR should only be asserted with PREADY
	apb_pslverr_requires_pready: assert property (@(posedge PCLK) PSLVERR |-> PREADY);

	// APB protocol: setup phase followed by access phase
	apb_access_phase: assert property (@(posedge PCLK) (PSELx && !PENABLE) |=> (PSELx && PENABLE));

	// TX FIFO cannot be both full and empty simultaneously
	tx_fifo_not_full_and_empty: assert property (@(posedge PCLK) !(i2c.TX_F_FULL && i2c.TX_F_EMPTY));

	// RX FIFO cannot be both full and empty simultaneously
	rx_fifo_not_full_and_empty: assert property (@(posedge PCLK) !(i2c.RX_F_FULL && i2c.RX_F_EMPTY));

	// No write to TX FIFO when full
	tx_no_write_when_full: assert property (@(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA);

	// No read from TX FIFO when empty
	tx_no_read_when_empty: assert property (@(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN);

	// No write to RX FIFO when full
	rx_no_write_when_full: assert property (@(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA);

	// No read from RX FIFO when empty
	rx_no_read_when_empty: assert property (@(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN);

	// During reset, outputs should be stable/known
	reset_no_pready: assert property (@(posedge PCLK) !PRESETn |-> !PREADY);

	// INT_RX and INT_TX should not both be asserted simultaneously (typical behavior)
	no_simultaneous_interrupts: assert property (@(posedge PCLK) !(INT_RX && INT_TX));

	// tx_empty signal consistency with TX FIFO empty
	tx_empty_consistency: assert property (@(posedge PCLK) PRESETn |-> (i2c.tx_empty == i2c.TX_F_EMPTY));

	// rx_empty signal consistency with RX FIFO empty
	rx_empty_consistency: assert property (@(posedge PCLK) PRESETn |-> (i2c.rx_empty == i2c.RX_F_EMPTY));

	// PRDATA should be stable when not in a read transaction
	prdata_known_during_read: assert property (@(posedge PCLK) (PSELx && PENABLE && !PWRITE && PREADY) |-> !$isunknown(PRDATA));

	// SDA and SCL enable should not be unknown when out of reset
	sda_enable_known: assert property (@(posedge PCLK) PRESETn |-> !$isunknown(SDA_ENABLE));
	scl_enable_known: assert property (@(posedge PCLK) PRESETn |-> !$isunknown(SCL_ENABLE));

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
