module module_i2c_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 14
)
(
	input PCLK,
	input PRESETn,
	input fifo_tx_f_full,
	input fifo_tx_f_empty,
	input [DWIDTH-1:0] fifo_tx_data_out,
	input fifo_rx_f_full,
	input fifo_rx_f_empty,
	input fifo_rx_wr_en,
	input [DWIDTH-1:0] fifo_rx_data_in,
	input [AWIDTH-1:0] DATA_CONFIG_REG,
	input [AWIDTH-1:0] TIMEOUT_TX,
	input fifo_tx_rd_en,
	input TX_EMPTY,
	input RX_EMPTY,
	input ERROR,
	input ENABLE_SDA,
	input ENABLE_SCL,
	input SDA,
	input SCL
);

	tx_empty_when_fifo_empty: assert property (@(posedge PCLK) fifo_tx_f_empty |-> TX_EMPTY);
	tx_empty_false_when_fifo_not_empty: assert property (@(posedge PCLK) !fifo_tx_f_empty |-> !TX_EMPTY);
	
	rx_empty_when_fifo_empty: assert property (@(posedge PCLK) fifo_rx_f_empty |-> RX_EMPTY);
	rx_empty_false_when_fifo_not_empty: assert property (@(posedge PCLK) !fifo_rx_f_empty |-> !RX_EMPTY);
	
	error_asserted_when_both_config_bits_set: assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> ERROR);
	error_deasserted_when_config_bits_not_both_set: assert property (@(posedge PCLK) !(DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> !ERROR);
	
	state_tx_resets_to_idle: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == 6'd0));
	state_rx_resets_to_idle: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == 6'd0));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
