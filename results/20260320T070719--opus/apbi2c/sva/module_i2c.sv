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

// ERROR is asserted when both config bits [0] and [1] are set
error_when_both_config_bits_set: assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b1);

// ERROR is deasserted when config bits [0] and [1] are not both set
no_error_when_config_bits_not_both_set: assert property (@(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b0);

// After reset, TX state machine goes to IDLE
reset_tx_state_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_tx == IDLE);

// After reset, RX state machine goes to IDLE
reset_rx_state_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_rx == IDLE);

// After reset, SDA_OUT is high
reset_sda_out_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT == 1'b1);

// After reset, BR_CLK_O is high
reset_br_clk_o_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O == 1'b1);

// After reset, fifo_tx_rd_en is low
reset_fifo_tx_rd_en_low: assert property (@(posedge PCLK) !PRESETn |=> fifo_tx_rd_en == 1'b0);

// After reset, count_send_data is zero
reset_count_send_data_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_send_data == 12'd0);

// After reset, count_tx is zero
reset_count_tx_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_tx == 2'd0);

// After reset, RESPONSE is zero
reset_response_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.RESPONSE == 1'b0);

// After reset, SDA_OUT_RX is low
reset_sda_out_rx_low: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT_RX == 1'b0);

// After reset, BR_CLK_O_RX is low
reset_br_clk_o_rx_low: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O_RX == 1'b0);

// After reset, fifo_rx_wr_en is low
reset_fifo_rx_wr_en_low: assert property (@(posedge PCLK) !PRESETn |=> fifo_rx_wr_en == 1'b0);

// After reset, count_receive_data is zero
reset_count_receive_data_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_receive_data == 12'd0);

// After reset, count_rx is zero
reset_count_rx_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_rx == 2'd0);

// After reset, count_timeout is zero
reset_count_timeout_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_timeout == 12'd0);

// TX state machine valid state range
tx_state_valid: assert property (@(posedge PCLK) PRESETn |-> module_i2c.state_tx <= 6'd40);

// RX state machine valid state range
rx_state_valid: assert property (@(posedge PCLK) PRESETn |-> module_i2c.state_rx <= 6'd40);

// In IDLE TX state, fifo_tx_rd_en must be low
idle_tx_no_read: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == IDLE) |=> fifo_tx_rd_en == 1'b0);

// ENABLE_SDA is low when TX state machine is in a response state (TX master releases SDA)
enable_sda_low_tx_response: assert property (@(posedge PCLK) (module_i2c.state_rx != RESPONSE_CIN && module_i2c.state_rx != RESPONSE_ADDRESS && module_i2c.state_rx != RESPONSE_DATA0_1 && module_i2c.state_rx != RESPONSE_DATA1_1 && (module_i2c.state_tx == RESPONSE_CIN || module_i2c.state_tx == RESPONSE_ADDRESS || module_i2c.state_tx == RESPONSE_DATA0_1 || module_i2c.state_tx == RESPONSE_DATA1_1)) |-> ENABLE_SDA == 1'b0);

// ENABLE_SDA is high when RX state machine is in a response state
enable_sda_high_rx_response: assert property (@(posedge PCLK) (module_i2c.state_rx == RESPONSE_CIN || module_i2c.state_rx == RESPONSE_ADDRESS || module_i2c.state_rx == RESPONSE_DATA0_1 || module_i2c.state_rx == RESPONSE_DATA1_1) |-> ENABLE_SDA == 1'b1);

// ENABLE_SCL is high when TX state machine is in a response state
enable_scl_high_tx_response: assert property (@(posedge PCLK) (module_i2c.state_tx == RESPONSE_CIN || module_i2c.state_tx == RESPONSE_ADDRESS || module_i2c.state_tx == RESPONSE_DATA0_1 || module_i2c.state_tx == RESPONSE_DATA1_1) |-> ENABLE_SCL == 1'b1);

// ENABLE_SCL is high when RX state machine is in a response state
enable_scl_high_rx_response: assert property (@(posedge PCLK) (module_i2c.state_rx == RESPONSE_CIN || module_i2c.state_rx == RESPONSE_ADDRESS || module_i2c.state_rx == RESPONSE_DATA0_1 || module_i2c.state_rx == RESPONSE_DATA1_1) |-> ENABLE_SCL == 1'b1);

// TX cannot leave IDLE unless config bit 0 is set and bit 1 is clear and FIFO has data
tx_idle_to_start_condition: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == IDLE && module_i2c.next_state_tx == START) |-> (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0)));

// RX cannot leave IDLE unless config bit 1 is set and bit 0 is clear
rx_idle_to_start_condition: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_rx == IDLE && module_i2c.next_state_rx == START) |-> (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1));

// fifo_tx_rd_en asserted only during RESPONSE_DATA1_1 completion
fifo_tx_rd_en_only_at_data1_response: assert property (@(posedge PCLK) (PRESETn && fifo_tx_rd_en == 1'b1) |-> (module_i2c.state_tx == RESPONSE_DATA1_1));

// STOP state always returns to IDLE for TX
tx_stop_goes_to_idle: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == IDLE);

// STOP state always returns to IDLE for RX
rx_stop_goes_to_idle: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_rx == STOP && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_rx == IDLE);

// count_tx never exceeds 3
count_tx_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.count_tx <= 2'd3);

// count_rx never exceeds 3
count_rx_range: assert property (@(posedge PCLK) PRESETn |-> module_i2c.count_rx <= 2'd3);

// When both config bits set, FSM stays in IDLE (TX)
tx_error_stays_idle: assert property (@(posedge PCLK) (PRESETn && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1 && module_i2c.state_tx == IDLE) |=> module_i2c.state_tx == IDLE);

// When both config bits set, FSM stays in IDLE (RX)
rx_error_stays_idle: assert property (@(posedge PCLK) (PRESETn && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1 && module_i2c.state_rx == IDLE) |=> module_i2c.state_rx == IDLE);

// In DELAY_BYTES TX state, fifo_tx_rd_en is deasserted
delay_bytes_tx_rd_en_low: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == DELAY_BYTES) |=> fifo_tx_rd_en == 1'b0);

// In NACK TX state, fifo_tx_rd_en is deasserted
nack_tx_rd_en_low: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == NACK) |=> fifo_tx_rd_en == 1'b0);

// BR_CLK_O is high in STOP state for TX
stop_br_clk_high: assert property (@(posedge PCLK) (PRESETn && module_i2c.state_tx == STOP) |=> module_i2c.BR_CLK_O == 1'b1);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
