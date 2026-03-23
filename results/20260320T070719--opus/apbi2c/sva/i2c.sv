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

// RESET_N is inverse of PRESETn
reset_n_active_when_presetn_low: assert property (@(posedge PCLK) (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1));
reset_n_inactive_when_presetn_high: assert property (@(posedge PCLK) (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0));

// TX_F_FULL mirrors w_full
tx_f_full_equals_w_full: assert property (@(posedge PCLK) 1'b1 |-> (i2c.TX_F_FULL == i2c.w_full));

// APB protocol: PENABLE requires PSELx in same cycle (setup phase before access phase)
apb_penable_requires_pselx: assert property (@(posedge PCLK) PENABLE |-> PSELx);

// APB protocol: PREADY only asserted during access phase
apb_pready_requires_penable: assert property (@(posedge PCLK) PREADY |-> (PSELx && PENABLE));

// APB protocol: PSLVERR only during completed transfer
apb_pslverr_requires_transfer: assert property (@(posedge PCLK) PSLVERR |-> (PSELx && PENABLE));

// During reset, TX FIFO should be empty (reset clears FIFO)
reset_tx_fifo_empty: assert property (@(posedge PCLK) (PRESETn == 1'b0) |=> (i2c.TX_F_EMPTY == 1'b1));

// During reset, RX FIFO should be empty
reset_rx_fifo_empty: assert property (@(posedge PCLK) (PRESETn == 1'b0) |=> (i2c.RX_F_EMPTY == 1'b1));

// TX FIFO cannot be both full and empty simultaneously
tx_fifo_not_full_and_empty: assert property (@(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_F_EMPTY);

// RX FIFO cannot be both full and empty simultaneously
rx_fifo_not_full_and_empty: assert property (@(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_F_EMPTY);

// TX write enable should not assert when TX FIFO is full
tx_no_write_when_full: assert property (@(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA);

// TX read enable should not assert when TX FIFO is empty
tx_no_read_when_empty: assert property (@(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN);

// RX write enable should not assert when RX FIFO is full
rx_no_write_when_full: assert property (@(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA);

// RX read enable should not assert when RX FIFO is empty
rx_no_read_when_empty: assert property (@(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN);

// tx_empty reflects TX FIFO empty status
tx_empty_matches_fifo: assert property (@(posedge PCLK) 1'b1 |-> (i2c.tx_empty == i2c.TX_F_EMPTY));

// rx_empty reflects RX FIFO empty status
rx_empty_matches_fifo: assert property (@(posedge PCLK) 1'b1 |-> (i2c.rx_empty == i2c.RX_F_EMPTY));

// Error should not be asserted during reset
no_error_during_reset: assert property (@(posedge PCLK) !PRESETn |=> !i2c.error);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
