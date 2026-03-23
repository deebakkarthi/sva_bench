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

	// Local parameters for state encoding
	localparam [5:0] IDLE = 6'd0,
		START = 6'd1,
		CONTROLIN_1 = 6'd2,
		CONTROLIN_2 = 6'd3,
		CONTROLIN_3 = 6'd4,
		CONTROLIN_4 = 6'd5,
		CONTROLIN_5 = 6'd6,
		CONTROLIN_6 = 6'd7,
		CONTROLIN_7 = 6'd8,
		CONTROLIN_8 = 6'd9,
		RESPONSE_CIN = 6'd10,
		ADDRESS_1 = 6'd11,
		ADDRESS_2 = 6'd12,
		ADDRESS_3 = 6'd13,
		ADDRESS_4 = 6'd14,
		ADDRESS_5 = 6'd15,
		ADDRESS_6 = 6'd16,
		ADDRESS_7 = 6'd17,
		ADDRESS_8 = 6'd18,
		RESPONSE_ADDRESS = 6'd19,
		DATA0_1 = 6'd20,
		DATA0_2 = 6'd21,
		DATA0_3 = 6'd22,
		DATA0_4 = 6'd23,
		DATA0_5 = 6'd24,
		DATA0_6 = 6'd25,
		DATA0_7 = 6'd26,
		DATA0_8 = 6'd27,
		RESPONSE_DATA0_1 = 6'd28,
		DATA1_1 = 6'd29,
		DATA1_2 = 6'd30,
		DATA1_3 = 6'd31,
		DATA1_4 = 6'd32,
		DATA1_5 = 6'd33,
		DATA1_6 = 6'd34,
		DATA1_7 = 6'd35,
		DATA1_8 = 6'd36,
		RESPONSE_DATA1_1 = 6'd37,
		DELAY_BYTES = 6'd38,
		NACK = 6'd39,
		STOP = 6'd40;

	// TX_EMPTY mirrors fifo_tx_f_empty
	tx_empty_reflects_fifo: assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

	// RX_EMPTY mirrors fifo_rx_f_empty
	rx_empty_reflects_fifo: assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

	// ERROR asserted when both config bits 0 and 1 are set
	error_when_both_config_bits_set: assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b1);

	// ERROR deasserted when config bits are not both set
	no_error_when_config_bits_not_both_set: assert property (@(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b0);

	// On reset, state_tx goes to IDLE
	reset_state_tx_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_tx == IDLE);

	// On reset, state_rx goes to IDLE
	reset_state_rx_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_rx == IDLE);

	// On reset, SDA_OUT is 1
	reset_sda_out_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT == 1'b1);

	// On reset, SDA_OUT_RX is 0
	reset_sda_out_rx_low: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT_RX == 1'b0);

	// On reset, BR_CLK_O is 1
	reset_br_clk_o_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O == 1'b1);

	// On reset, BR_CLK_O_RX is 0
	reset_br_clk_o_rx_low: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O_RX == 1'b0);

	// On reset, fifo_tx_rd_en is 0
	reset_fifo_tx_rd_en: assert property (@(posedge PCLK) !PRESETn |=> fifo_tx_rd_en == 1'b0);

	// On reset, fifo_rx_wr_en is 0
	reset_fifo_rx_wr_en: assert property (@(posedge PCLK) !PRESETn |=> fifo_rx_wr_en == 1'b0);

	// On reset, count_send_data is 0
	reset_count_send_data: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_send_data == 12'd0);

	// On reset, count_receive_data is 0
	reset_count_receive_data: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_receive_data == 12'd0);

	// On reset, count_tx is 0
	reset_count_tx: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_tx == 2'd0);

	// On reset, count_rx is 0
	reset_count_rx: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_rx == 2'd0);

	// On reset, RESPONSE is 0
	reset_response: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.RESPONSE == 1'b0);

	// On reset, count_timeout is 0
	reset_count_timeout: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_timeout == 12'd0);

	// state_tx must be a valid state (0 to 40)
	state_tx_valid_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.state_tx <= 6'd40);

	// state_rx must be a valid state (0 to 40)
	state_rx_valid_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.state_rx <= 6'd40);

	// count_tx must be in valid range (0 to 3)
	count_tx_valid_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.count_tx <= 2'd3);

	// count_rx must be in valid range (0 to 3)
	count_rx_valid_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.count_rx <= 2'd3);

	// TX state machine stays IDLE when not enabled (config bit 0 = 0)
	tx_idle_when_disabled: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0 |=> module_i2c.state_tx == IDLE);

	// TX state machine stays IDLE on error condition
	tx_idle_on_error: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1 |=> module_i2c.state_tx == IDLE);

	// RX state machine stays IDLE when not enabled
	rx_idle_when_disabled: assert property (@(posedge PCLK) PRESETn && module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0 |=> module_i2c.state_rx == IDLE);

	// RX state machine stays IDLE on error condition
	rx_idle_on_error: assert property (@(posedge PCLK) PRESETn && module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1 |=> module_i2c.state_rx == IDLE);

	// fifo_tx_rd_en only asserted in RESPONSE_DATA1_1 state when count reaches limit
	fifo_tx_rd_en_only_in_response_data1: assert property (@(posedge PCLK) PRESETn && fifo_tx_rd_en |-> (module_i2c.state_tx == RESPONSE_DATA1_1 || $past(module_i2c.state_tx) == RESPONSE_DATA1_1));

	// STOP state transitions to IDLE when count completes
	stop_to_idle_tx: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] |=> module_i2c.state_tx == IDLE);

	// STOP state transitions to IDLE for RX when count completes
	stop_to_idle_rx: assert property (@(posedge PCLK) PRESETn && module_i2c.state_rx == STOP && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] |=> module_i2c.state_rx == IDLE);

	// ENABLE_SDA is 0 when TX is in response state and RX is not in response state
	enable_sda_low_in_tx_response: assert property (@(posedge PCLK)
		(module_i2c.state_rx != RESPONSE_CIN && module_i2c.state_rx != RESPONSE_ADDRESS && module_i2c.state_rx != RESPONSE_DATA0_1 && module_i2c.state_rx != RESPONSE_DATA1_1) &&
		(module_i2c.state_tx == RESPONSE_CIN || module_i2c.state_tx == RESPONSE_ADDRESS || module_i2c.state_tx == RESPONSE_DATA0_1 || module_i2c.state_tx == RESPONSE_DATA1_1)
		|-> ENABLE_SDA == 1'b0);

	// ENABLE_SDA is 1 when RX is in response state
	enable_sda_high_in_rx_response: assert property (@(posedge PCLK)
		(module_i2c.state_rx == RESPONSE_CIN || module_i2c.state_rx == RESPONSE_ADDRESS || module_i2c.state_rx == RESPONSE_DATA0_1 || module_i2c.state_rx == RESPONSE_DATA1_1)
		|-> ENABLE_SDA == 1'b1);

	// ENABLE_SCL is 1 when either TX or RX is in response state
	enable_scl_high_in_response: assert property (@(posedge PCLK)
		(module_i2c.state_rx == RESPONSE_CIN || module_i2c.state_rx == RESPONSE_ADDRESS || module_i2c.state_rx == RESPONSE_DATA0_1 || module_i2c.state_rx == RESPONSE_DATA1_1 ||
		 module_i2c.state_tx == RESPONSE_CIN || module_i2c.state_tx == RESPONSE_ADDRESS || module_i2c.state_tx == RESPONSE_DATA0_1 || module_i2c.state_tx == RESPONSE_DATA1_1)
		|-> ENABLE_SCL == 1'b1);

	// ENABLE_SCL is 0 when neither TX nor RX is in response state
	enable_scl_low_not_in_response: assert property (@(posedge PCLK)
		(module_i2c.state_rx != RESPONSE_CIN && module_i2c.state_rx != RESPONSE_ADDRESS && module_i2c.state_rx != RESPONSE_DATA0_1 && module_i2c.state_rx != RESPONSE_DATA1_1) &&
		(module_i2c.state_tx != RESPONSE_CIN && module_i2c.state_tx != RESPONSE_ADDRESS && module_i2c.state_tx != RESPONSE_DATA0_1 && module_i2c.state_tx != RESPONSE_DATA1_1)
		|-> ENABLE_SCL == 1'b0);

	// In TX IDLE state, fifo_tx_rd_en should be deasserted
	idle_tx_rd_en_low: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE |=> fifo_tx_rd_en == 1'b0);

	// START state must follow IDLE when conditions met for TX
	idle_to_start_tx: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0 && ((fifo_tx_f_empty == 1'b0 && fifo_tx_f_full == 1'b0) || fifo_tx_f_full == 1'b1) && module_i2c.count_timeout < TIMEOUT_TX |=> module_i2c.state_tx == START);

	// CONTROLIN_1 follows START when count matches
	start_to_controlin1: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == START && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] |=> module_i2c.state_tx == CONTROLIN_1);

	// After RESPONSE_CIN with ACK, go to DELAY_BYTES
	response_cin_ack_to_delay: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == RESPONSE_CIN && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0 |=> module_i2c.state_tx == DELAY_BYTES);

	// After RESPONSE_CIN with NACK, go to NACK state
	response_cin_nack_to_nack: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == RESPONSE_CIN && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1 |=> module_i2c.state_tx == NACK);

	// count_send_data should not exceed the configured value under normal operation
	count_send_bounded: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx != NACK && module_i2c.state_tx != IDLE |-> module_i2c.count_send_data <= DATA_CONFIG_REG[13:2]);

	// SDA_OUT should be high in IDLE when module is not active
	sda_out_high_idle_inactive: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0 |=> module_i2c.SDA_OUT == 1'b1);

	// BR_CLK_O should be high in IDLE when module is not active
	br_clk_high_idle_inactive: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0 |=> module_i2c.BR_CLK_O == 1'b1);

	// In DELAY_BYTES state, fifo_tx_rd_en should be 0
	delay_bytes_rd_en_low: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == DELAY_BYTES |=> fifo_tx_rd_en == 1'b0);

	// BR_CLK_O should be high during STOP state
	br_clk_high_during_stop: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == STOP |=> module_i2c.BR_CLK_O == 1'b1);

	// DELAY_BYTES with count_tx==3 goes to STOP
	delay_bytes_count3_to_stop: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd3 |=> module_i2c.state_tx == STOP);

	// DELAY_BYTES with count_tx==0 goes to ADDRESS_1
	delay_bytes_count0_to_addr1: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd0 |=> module_i2c.state_tx == ADDRESS_1);

	// DELAY_BYTES with count_tx==1 goes to DATA0_1
	delay_bytes_count1_to_data0: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd1 |=> module_i2c.state_tx == DATA0_1);

	// DELAY_BYTES with count_tx==2 goes to DATA1_1
	delay_bytes_count2_to_data1: assert property (@(posedge PCLK) PRESETn && module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd2 |=> module_i2c.state_tx == DATA1_1);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
