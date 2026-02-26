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

a_reset_active_when_preset_low : assert property (@(posedge PCLK) 
  (PRESETn == 1'b0) |-> (i2c.RESET_N == 1'b1)
);

a_reset_inactive_when_preset_high : assert property (@(posedge PCLK) 
  (PRESETn == 1'b1) |-> (i2c.RESET_N == 1'b0)
);

a_tx_fifo_no_write_when_full : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  !(i2c.TX_WRITE_ENA == 1'b1 && i2c.TX_F_FULL == 1'b1)
);

a_tx_fifo_no_read_when_empty : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  !(i2c.TX_RD_EN == 1'b1 && i2c.TX_F_EMPTY == 1'b1)
);

a_rx_fifo_no_write_when_full : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  !(i2c.RX_WRITE_ENA == 1'b1 && i2c.RX_F_FULL == 1'b1)
);

a_rx_fifo_no_read_when_empty : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  !(i2c.RX_RD_EN == 1'b1 && i2c.RX_F_EMPTY == 1'b1)
);

a_apb_penable_requires_pselx : assert property (@(posedge PCLK)
  (PENABLE == 1'b1) |-> (PSELx == 1'b1)
);

a_apb_pready_driven_on_transfer : assert property (@(posedge PCLK)
  (PSELx == 1'b1 && PENABLE == 1'b1) |-> ((PREADY == 1'b0) || (PREADY == 1'b1))
);

a_apb_pslverr_driven_on_transfer : assert property (@(posedge PCLK)
  (PSELx == 1'b1 && PENABLE == 1'b1) |-> ((PSLVERR == 1'b0) || (PSLVERR == 1'b1))
);

a_sda_open_drain_logic : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (SDA_ENABLE == 1'b1) |-> (SDA == 1'b0)
);

a_scl_open_drain_logic : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (SCL_ENABLE == 1'b1) |-> (SCL == 1'b0)
);

a_tx_full_prevents_write : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (i2c.TX_F_FULL == 1'b1) |-> (i2c.TX_WRITE_ENA == 1'b0)
);

a_rx_empty_prevents_read : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (i2c.RX_F_EMPTY == 1'b1) |-> (i2c.RX_RD_EN == 1'b0)
);

a_tx_empty_flag_consistency : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (i2c.tx_empty == 1'b1) |-> (i2c.TX_F_EMPTY == 1'b1)
);

a_rx_empty_flag_consistency : assert property (@(posedge PCLK) disable iff (PRESETn == 1'b0)
  (i2c.rx_empty == 1'b1) |-> (i2c.RX_F_EMPTY == 1'b1)
);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
