module module_i2c_assert #(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 14
)(
    input PCLK,
    input PRESETn,
    input fifo_tx_f_full,
    input fifo_tx_f_empty,
    input [DWIDTH-1:0] fifo_tx_data_out,
    input fifo_rx_f_full,
    input fifo_rx_f_empty,
    output reg fifo_rx_wr_en,
    output reg [DWIDTH-1:0] fifo_rx_data_in,
    input [AWIDTH-1:0] DATA_CONFIG_REG,
    input [AWIDTH-1:0] TIMEOUT_TX,
    output reg fifo_tx_rd_en,
    output TX_EMPTY,
    output RX_EMPTY,
    output ERROR,
    output ENABLE_SDA,
    output ENABLE_SCL,
    inout SDA,
    inout SCL
);

// TX_EMPTY reflects fifo_tx_f_empty
tx_empty_when_fifo_empty: assert property (
    @(posedge PCLK) (fifo_tx_f_empty == 1'b1) |-> (TX_EMPTY == 1'b1)
);

tx_empty_when_fifo_not_empty: assert property (
    @(posedge PCLK) (fifo_tx_f_empty == 1'b0) |-> (TX_EMPTY == 1'b0)
);

// RX_EMPTY reflects fifo_rx_f_empty
rx_empty_when_fifo_empty: assert property (
    @(posedge PCLK) (fifo_rx_f_empty == 1'b1) |-> (RX_EMPTY == 1'b1)
);

rx_empty_when_fifo_not_empty: assert property (
    @(posedge PCLK) (fifo_rx_f_empty == 1'b0) |-> (RX_EMPTY == 1'b0)
);

// ERROR signal: only when both config bits set
error_when_both_config_bits_set: assert property (
    @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1)
);

error_not_when_config_bit0_clear: assert property (
    @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b0) |-> (ERROR == 1'b0)
);

error_not_when_config_bit1_clear: assert property (
    @(posedge PCLK) (DATA_CONFIG_REG[1] == 1'b0) |-> (ERROR == 1'b0)
);

// Reset behavior for TX state machine
reset_tx_state_to_idle: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_tx == 6'd0)
);

reset_tx_count_send_data: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_send_data == 12'd0)
);

reset_fifo_tx_rd_en: assert property (
    @(posedge PCLK) (!PRESETn) |=> (fifo_tx_rd_en == 1'b0)
);

reset_count_tx: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_tx == 2'd0)
);

// Reset behavior for RX state machine
reset_rx_state_to_idle: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_rx == 6'd0)
);

reset_count_receive_data: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_receive_data == 12'd0)
);

reset_fifo_rx_wr_en: assert property (
    @(posedge PCLK) (!PRESETn) |=> (fifo_rx_wr_en == 1'b0)
);

reset_count_rx: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_rx == 2'd0)
);

reset_br_clk_o: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O == 1'b1)
);

reset_br_clk_o_rx: assert property (
    @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O_RX == 1'b0)
);

// TX state machine valid state range (0 to 40)
tx_state_valid_range: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx <= 6'd40)
);

// RX state machine valid state range (0 to 40)
rx_state_valid_range: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx <= 6'd40)
);

// count_tx stays within 2-bit range (always true for 2-bit reg, but verify no overflow beyond 3)
count_tx_valid_range: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.count_tx <= 2'd3)
);

// count_rx stays within 2-bit range
count_rx_valid_range: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.count_rx <= 2'd3)
);

// TX FSM: IDLE stays in IDLE when not enabled
tx_idle_stays_idle_when_disabled: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b0 &&
     (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
     DATA_CONFIG_REG[1] == 1'b0)
    |=> (module_i2c.state_tx == 6'd0)
);

// TX FSM: IDLE transitions to IDLE when error config
tx_idle_stays_idle_when_error_config: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 &&
     (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
     DATA_CONFIG_REG[1] == 1'b1)
    |=> (module_i2c.state_tx == 6'd0)
);

// TX FSM: IDLE transitions to START when enabled with data and no error
tx_idle_to_start: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 &&
     ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
     DATA_CONFIG_REG[1] == 1'b0 &&
     module_i2c.count_timeout < TIMEOUT_TX)
    |=> (module_i2c.state_tx == 6'd1)
);

// TX FSM: STOP transitions to IDLE when count reached
tx_stop_to_idle: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd40 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd0)
);

// TX FSM: START transitions to CONTROLIN_1 when count reached
tx_start_to_controlin1: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd2)
);

// TX FSM: CONTROLIN_8 transitions to RESPONSE_CIN when count reached
tx_controlin8_to_response_cin: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd9 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd10)
);

// TX FSM: RESPONSE_CIN with ACK goes to DELAY_BYTES
tx_response_cin_ack_to_delay: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

// TX FSM: RESPONSE_CIN with NACK goes to NACK state
tx_response_cin_nack_to_nack: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1)
    |=> (module_i2c.state_tx == 6'd39)
);

// TX FSM: ADDRESS_8 transitions to RESPONSE_ADDRESS when count reached
tx_address8_to_response_address: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd18 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd19)
);

// TX FSM: RESPONSE_ADDRESS with ACK goes to DELAY_BYTES
tx_response_address_ack_to_delay: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd19 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

// TX FSM: DATA0_8 transitions to RESPONSE_DATA0_1 when count reached
tx_data08_to_response_data0: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd27 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd28)
);

// TX FSM: DATA1_8 transitions to RESPONSE_DATA1_1 when count reached
tx_data18_to_response_data1: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd36 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd37)
);

// TX FSM: DELAY_BYTES with count_tx==3 goes to STOP
tx_delay_bytes_count3_to_stop: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd3)
    |=> (module_i2c.state_tx == 6'd40)
);

// TX FSM: DELAY_BYTES with count_tx==0 goes to ADDRESS_1
tx_delay_bytes_count0_to_address1: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd0)
    |=> (module_i2c.state_tx == 6'd11)
);

// TX FSM: DELAY_BYTES with count_tx==1 goes to DATA0_1
tx_delay_bytes_count1_to_data01: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd1)
    |=> (module_i2c.state_tx == 6'd20)
);

// TX FSM: DELAY_BYTES with count_tx==2 goes to DATA1_1
tx_delay_bytes_count2_to_data11: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd2)
    |=> (module_i2c.state_tx == 6'd29)
);

// TX FSM: state stays in same state when count not reached (spot check with START)
tx_start_stays_while_counting: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 &&
     module_i2c.count_send_data != DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd1)
);

// fifo_tx_rd_en is deasserted in IDLE
tx_rd_en_idle_deasserted: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0)
    |=> (fifo_tx_rd_en == 1'b0)
);

// fifo_tx_rd_en is deasserted in DELAY_BYTES
tx_rd_en_delay_bytes_deasserted: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38)
    |=> (fifo_tx_rd_en == 1'b0)
);

// RX FSM: IDLE stays in IDLE when both config bits clear
rx_idle_stays_idle_both_clear: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b0 &&
     DATA_CONFIG_REG[1] == 1'b0)
    |=> (module_i2c.state_rx == 6'd0)
);

// RX FSM: IDLE stays in IDLE when both config bits set
rx_idle_stays_idle_both_set: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 &&
     DATA_CONFIG_REG[1] == 1'b1)
    |=> (module_i2c.state_rx == 6'd0)
);

// RX FSM: STOP transitions to IDLE when count reached
rx_stop_to_idle: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd0)
);

// RX FSM valid state range
rx_state_valid_range_check: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx != 6'd41) &&
    (module_i2c.state_rx != 6'd42) &&
    (module_i2c.state_rx != 6'd63)
);

// ENABLE_SDA behavior: high when rx is in response states
enable_sda_high_in_rx_response_cin: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd10)
    |-> (ENABLE_SDA == 1'b1)
);

enable_sda_high_in_rx_response_address: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd19)
    |-> (ENABLE_SDA == 1'b1)
);

// ENABLE_SCL: high when rx is in response states
enable_scl_high_in_rx_response_cin: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd10)
    |-> (ENABLE_SCL == 1'b1)
);

// count_timeout resets when not in IDLE or IDLE condition not met
count_timeout_reset_when_not_idle: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx != 6'd0)
    |=> (module_i2c.count_timeout == 12'd0)
);

// count_timeout bounded by TIMEOUT_TX
count_timeout_bounded: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.count_timeout <= TIMEOUT_TX + 12'd1)
);

// fifo_rx_wr_en deasserted in STOP state
rx_wr_en_deasserted_in_stop: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40)
    |=> (fifo_rx_wr_en == 1'b0)
);

// Sequential state transitions: consecutive CONTROLIN states for TX
tx_controlin1_to_controlin2: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd2 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd3)
);

tx_controlin2_to_controlin3: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd3 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd4)
);

tx_controlin3_to_controlin4: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd4 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd5)
);

tx_controlin4_to_controlin5: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd5 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd6)
);

tx_controlin5_to_controlin6: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd6 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd7)
);

tx_controlin6_to_controlin7: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd7 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd8)
);

tx_controlin7_to_controlin8: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd8 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd9)
);

// ADDRESS sequential transitions for TX
tx_address1_to_address2: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd11 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd12)
);

tx_address7_to_address8: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd17 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd18)
);

// DATA0 sequential transitions
tx_data01_to_data02: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd20 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd21)
);

// DATA1 sequential transitions
tx_data11_to_data12: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd29 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd30)
);

// RX FSM sequential controlin transitions
rx_controlin1_to_controlin2: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd2 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd3)
);

rx_controlin8_to_response_cin: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd9 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd10)
);

rx_address8_to_response_address: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd18 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd19)
);

rx_data08_to_response_data0: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd27 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd28)
);

rx_data18_to_response_data1: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd36 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd37)
);

// RX DELAY_BYTES with count_rx==3 goes to STOP
rx_delay_bytes_count3_to_stop: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd3)
    |=> (module_i2c.state_rx == 6'd40)
);

// RX DELAY_BYTES with count_rx==0 goes to ADDRESS_1
rx_delay_bytes_count0_to_address1: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd0)
    |=> (module_i2c.state_rx == 6'd11)
);

// RX DELAY_BYTES with count_rx==1 goes to DATA0_1
rx_delay_bytes_count1_to_data01: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd1)
    |=> (module_i2c.state_rx == 6'd20)
);

// RX DELAY_BYTES with count_rx==2 goes to DATA1_1
rx_delay_bytes_count2_to_data11: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd2)
    |=> (module_i2c.state_rx == 6'd29)
);

// RESPONSE_DATA1_1 ACK to DELAY_BYTES for TX
tx_response_data1_ack_to_delay: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd37 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

// RESPONSE_DATA1_1 NACK to NACK for TX
tx_response_data1_nack_to_nack: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd37 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1)
    |=> (module_i2c.state_tx == 6'd39)
);

// count_send_data increments by 1 when less than DATA_CONFIG_REG[13:2] in non-IDLE active TX states
tx_count_send_increments_in_start: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 &&
     module_i2c.count_send_data < DATA_CONFIG_REG[13:2])
    |=> (module_i2c.count_send_data == $past(module_i2c.count_send_data) + 12'd1)
);

// count_send_data resets to 0 after reaching DATA_CONFIG_REG[13:2] in START state
tx_count_send_resets_in_start: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.count_send_data == 12'd0)
);

// RESPONSE signal is only 0 or 1 (always true for 1-bit reg, sanity check)
response_valid: assert property (
    @(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.RESPONSE == 1'b0 || module_i2c.RESPONSE == 1'b1)
);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
