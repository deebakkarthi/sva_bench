module module_i2c_assert#(
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
		 output fifo_rx_wr_en,
		 output [DWIDTH-1:0] fifo_rx_data_in, 

		 input [AWIDTH-1:0] DATA_CONFIG_REG,
 		 input [AWIDTH-1:0] TIMEOUT_TX,
		
		 output fifo_tx_rd_en,
		 output TX_EMPTY,
		 output RX_EMPTY,
		 output ERROR,
		 output ENABLE_SDA,
		 output ENABLE_SCL,

		 inout SDA,
		 inout SCL
		 );

tx_empty_tracks_fifo: assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

rx_empty_tracks_fifo: assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

error_when_config_both_set: assert property (@(posedge PCLK) 
	(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1));

error_when_config_not_both_set: assert property (@(posedge PCLK)
	!(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b0));

no_tx_read_on_empty: assert property (@(posedge PCLK)
	fifo_tx_f_empty == 1'b1 |-> fifo_tx_rd_en == 1'b0);

reset_initialize_state_tx: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.state_tx == 6'd0));

reset_initialize_state_rx: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.state_rx == 6'd0));

reset_initialize_count_send_data: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.count_send_data == 12'd0));

reset_initialize_count_receive_data: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.count_receive_data == 12'd0));

reset_sda_out_high: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.SDA_OUT == 1'b1));

reset_br_clk_high: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.BR_CLK_O == 1'b1));

reset_fifo_tx_rd_en_low: assert property (@(posedge PCLK)
	!PRESETn |=> (fifo_tx_rd_en == 1'b0));

reset_fifo_rx_wr_en_low: assert property (@(posedge PCLK)
	!PRESETn |=> (fifo_rx_wr_en == 1'b0));

reset_count_tx_zero: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.count_tx == 2'd0));

reset_count_rx_zero: assert property (@(posedge PCLK)
	!PRESETn |=> (module_i2c_u.count_rx == 2'd0));

enable_sda_in_rx_response_states: assert property (@(posedge PCLK)
	(module_i2c_u.state_rx == 6'd10 || module_i2c_u.state_rx == 6'd19 || 
	 module_i2c_u.state_rx == 6'd28 || module_i2c_u.state_rx == 6'd37) |-> ENABLE_SDA == 1'b1);

enable_sda_in_tx_response_states: assert property (@(posedge PCLK)
	(module_i2c_u.state_tx == 6'd10 || module_i2c_u.state_tx == 6'd19 || 
	 module_i2c_u.state_tx == 6'd28 || module_i2c_u.state_tx == 6'd37) |-> ENABLE_SDA == 1'b0);

enable_scl_in_response_states: assert property (@(posedge PCLK)
	(module_i2c_u.state_rx == 6'd10 || module_i2c_u.state_rx == 6'd19 || 
	 module_i2c_u.state_rx == 6'd28 || module_i2c_u.state_rx == 6'd37 ||
	 module_i2c_u.state_tx == 6'd10 || module_i2c_u.state_tx == 6'd19 || 
	 module_i2c_u.state_tx == 6'd28 || module_i2c_u.state_tx == 6'd37) |-> ENABLE_SCL == 1'b1);

count_timeout_bounds: assert property (@(posedge PCLK)
	module_i2c_u.count_timeout <= 12'd4095);

fifo_rx_wr_en_low_in_idle: assert property (@(posedge PCLK)
	module_i2c_u.state_rx == 6'd0 |-> fifo_rx_wr_en == 1'b0);

fifo_rx_wr_en_low_in_stop: assert property (@(posedge PCLK)
	module_i2c_u.state_rx == 6'd40 |-> fifo_rx_wr_en == 1'b0);

fifo_tx_rd_en_low_in_idle: assert property (@(posedge PCLK)
	module_i2c_u.state_tx == 6'd0 |-> fifo_tx_rd_en == 1'b0);

sda_config_disabled_blocks_tx: assert property (@(posedge PCLK)
	DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0 |-> 
	module_i2c_u.state_tx == 6'd0);

sda_disabled_allows_rx: assert property (@(posedge PCLK)
	DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1 |-> 
	(module_i2c_u.state_rx != 6'd0 || module_i2c_u.SDA_OUT_RX == module_i2c_u.SDA_OUT_RX));

count_send_data_increments: assert property (@(posedge PCLK)
	(module_i2c_u.state_tx != 6'd0 && module_i2c_u.count_send_data < DATA_CONFIG_REG[13:2]) |=>
	module_i2c_u.count_send_data > $past(module_i2c_u.count_send_data));

count_receive_data_increments: assert property (@(posedge PCLK)
	(module_i2c_u.state_rx != 6'd0 && module_i2c_u.count_receive_data < DATA_CONFIG_REG[13:2]) |=>
	module_i2c_u.count_receive_data > $past(module_i2c_u.count_receive_data));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
