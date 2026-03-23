module module_i2c_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 14
) (
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

tx_empty_reflects_fifo: assert property (TX_EMPTY == fifo_tx_f_empty);

rx_empty_reflects_fifo: assert property (RX_EMPTY == fifo_rx_f_empty);

error_from_config_bits: assert property (ERROR == (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]));

tx_no_read_when_empty: assert property (@(posedge PCLK) disable iff (!PRESETn) fifo_tx_f_empty |-> !fifo_tx_rd_en);

rx_no_write_when_full: assert property (@(posedge PCLK) disable iff (!PRESETn) fifo_rx_f_full |-> !fifo_rx_wr_en);

tx_state_reset_to_idle: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.state_tx == 6'd0);

rx_state_reset_to_idle: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.state_rx == 6'd0);

tx_counter_reset: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.count_send_data == 12'd0);

rx_counter_reset: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.count_receive_data == 12'd0);

sda_out_reset_high: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.SDA_OUT == 1'b1);

sda_out_rx_reset_low: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.SDA_OUT_RX == 1'b0);

br_clk_o_reset_high: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.BR_CLK_O == 1'b1);

br_clk_o_rx_reset_low: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.BR_CLK_O_RX == 1'b0);

response_reset_low: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.RESPONSE == 1'b0);

timeout_counter_reset: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.count_timeout == 12'd0);

tx_rd_en_reset_low: assert property (@(posedge PCLK) !PRESETn |-> fifo_tx_rd_en == 1'b0);

rx_wr_en_reset_low: assert property (@(posedge PCLK) !PRESETn |-> fifo_rx_wr_en == 1'b0);

tx_count_tx_reset: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.count_tx == 2'd0);

rx_count_rx_reset: assert property (@(posedge PCLK) !PRESETn |-> module_i2c.count_rx == 2'd0);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
