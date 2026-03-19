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

// APB Protocol Assertions

apb_pready_latency: assert property (@(posedge PCLK) (PSELx && PENABLE) |-> ##[0:10] PREADY);

apb_pready_requires_pselx: assert property (@(posedge PCLK) PREADY |-> PSELx);

apb_no_err_with_ready: assert property (@(posedge PCLK) !(PSLVERR && PREADY));

// TX FIFO State Assertions

tx_fifo_valid_state: assert property (@(posedge PCLK) !(i2c.TX_F_EMPTY && i2c.TX_F_FULL));

tx_fifo_no_read_empty: assert property (@(posedge PCLK) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN);

tx_fifo_no_write_full: assert property (@(posedge PCLK) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA);

// RX FIFO State Assertions

rx_fifo_valid_state: assert property (@(posedge PCLK) !(i2c.RX_F_EMPTY && i2c.RX_F_FULL));

rx_fifo_no_read_empty: assert property (@(posedge PCLK) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN);

rx_fifo_no_write_full: assert property (@(posedge PCLK) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA);

// Reset Assertions

tx_fifo_empty_post_reset: assert property (@(posedge PCLK) !PRESETn |=> i2c.TX_F_EMPTY);

rx_fifo_empty_post_reset: assert property (@(posedge PCLK) !PRESETn |=> i2c.RX_F_EMPTY);

// Interrupt Coherency Assertions

int_rx_has_data: assert property (@(posedge PCLK) INT_RX |-> !i2c.RX_F_EMPTY);

int_tx_has_data: assert property (@(posedge PCLK) INT_TX |-> !i2c.TX_F_EMPTY);

// I2C Bus Open-Drain Assertions

sda_open_drain: assert property (@(posedge PCLK) (SDA == 1'b0) |-> (SDA_ENABLE == 1'b1));

scl_open_drain: assert property (@(posedge PCLK) (SCL == 1'b0) |-> (SCL_ENABLE == 1'b1));

// Error Signal Coherency

error_assertion_coherent: assert property (@(posedge PCLK) i2c.error |-> (PRESETn == 1'b1));

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
