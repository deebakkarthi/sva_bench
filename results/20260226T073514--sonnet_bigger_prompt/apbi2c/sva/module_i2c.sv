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
tx_empty_correct: assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

// RX_EMPTY reflects fifo_rx_f_empty
rx_empty_correct: assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

// ERROR is only high when both config bits are set
error_condition: assert property (@(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1));

// After reset, state_tx should be IDLE (6'd0)
reset_state_tx: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == 6'd0));

// After reset, state_rx should be IDLE (6'd0)
reset_state_rx: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == 6'd0));

// After reset, count_send_data should be 0
reset_count_send_data: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0));

// After reset, count_receive_data should be 0
reset_count_receive_data: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0));

// After reset, fifo_tx_rd_en should be 0
reset_fifo_tx_rd_en: assert property (@(posedge PCLK) !PRESETn |=> (fifo_tx_rd_en == 1'b0));

// After reset, fifo_rx_wr_en should be 0
reset_fifo_rx_wr_en: assert property (@(posedge PCLK) !PRESETn |=> (fifo_rx_wr_en == 1'b0));

// After reset, count_tx should be 0
reset_count_tx: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_tx == 2'd0));

// After reset, count_rx should be 0
reset_count_rx: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_rx == 2'd0));

// After reset, BR_CLK_O should be 1
reset_br_clk_o: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1));

// After reset, BR_CLK_O_RX should be 0
reset_br_clk_o_rx: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O_RX == 1'b0));

// state_tx is always a valid state (0 to 40)
state_tx_valid: assert property (@(posedge PCLK) disable iff (!PRESETn) (module_i2c.state_tx <= 6'd40));

// state_rx is always a valid state (0 to 40)
state_rx_valid: assert property (@(posedge PCLK) disable iff (!PRESETn) (module_i2c.state_rx <= 6'd40));

// count_tx is always between 0 and 3
count_tx_bounded: assert property (@(posedge PCLK) disable iff (!PRESETn) (module_i2c.count_tx <= 2'd3));

// count_rx is always between 0 and 3
count_rx_bounded: assert property (@(posedge PCLK) disable iff (!PRESETn) (module_i2c.count_rx <= 2'd3));

// When both DATA_CONFIG_REG[0]==0 and DATA_CONFIG_REG[1]==0, TX FSM stays in IDLE
tx_idle_stays_idle_disabled: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] == 1'b0 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b0)
    |=> (module_i2c.state_tx == 6'd0));

// When DATA_CONFIG_REG[0]==1 and DATA_CONFIG_REG[1]==1, TX FSM stays in IDLE
tx_idle_stays_idle_error: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] == 1'b1 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b1)
    |=> (module_i2c.state_tx == 6'd0));

// TX FSM: IDLE goes to START only under correct conditions
tx_idle_to_start: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0 &&
     ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
     module_i2c.count_timeout < TIMEOUT_TX)
    |=> (module_i2c.state_tx == 6'd1));

// TX FSM: STOP goes back to IDLE
tx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd40 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd0));

// RX FSM: STOP goes back to IDLE
rx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd0));

// count_send_data resets to 0 after reaching DATA_CONFIG_REG[13:2]
count_send_data_reset: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx != 6'd0 &&
     module_i2c.state_tx != 6'd39 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.count_send_data == 12'd0));

// count_receive_data stays non-negative (unsigned)
count_receive_data_nonneg: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.count_receive_data >= 12'd0));

// ENABLE_SDA: when rx state is a response state, ENABLE_SDA is 1
enable_sda_rx_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd10 ||
     module_i2c.state_rx == 6'd19 ||
     module_i2c.state_rx == 6'd28 ||
     module_i2c.state_rx == 6'd37)
    |-> (ENABLE_SDA == 1'b1));

// ENABLE_SCL: when rx state is a response state, ENABLE_SCL is 1
enable_scl_rx_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd10 ||
     module_i2c.state_rx == 6'd19 ||
     module_i2c.state_rx == 6'd28 ||
     module_i2c.state_rx == 6'd37)
    |-> (ENABLE_SCL == 1'b1));

// ENABLE_SCL: when tx state is a response state (not rx), ENABLE_SCL is 1
enable_scl_tx_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (!(module_i2c.state_rx == 6'd10 ||
       module_i2c.state_rx == 6'd19 ||
       module_i2c.state_rx == 6'd28 ||
       module_i2c.state_rx == 6'd37) &&
     (module_i2c.state_tx == 6'd10 ||
      module_i2c.state_tx == 6'd19 ||
      module_i2c.state_tx == 6'd28 ||
      module_i2c.state_tx == 6'd37))
    |-> (ENABLE_SCL == 1'b1));

// fifo_tx_rd_en is deasserted in IDLE state (next cycle after entering IDLE)
fifo_tx_rd_en_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0) |-> (fifo_tx_rd_en == 1'b0));

// fifo_tx_rd_en is deasserted in DELAY_BYTES state
fifo_tx_rd_en_delay: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38) |-> ##1 (fifo_tx_rd_en == 1'b0));

// TX FSM: CONTROLIN_1 transitions to CONTROLIN_2 when count reaches threshold
tx_ctrl1_to_ctrl2: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd3));

// TX FSM: CONTROLIN_8 transitions to RESPONSE_CIN when count reaches threshold
tx_ctrl8_to_response_cin: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd9 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd10));

// TX FSM: ADDRESS_8 transitions to RESPONSE_ADDRESS when count reaches threshold
tx_addr8_to_response_addr: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd18 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd19));

// TX FSM: DATA0_8 transitions to RESPONSE_DATA0_1 when count reaches threshold
tx_data08_to_response_data0: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd27 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd28));

// TX FSM: DATA1_8 transitions to RESPONSE_DATA1_1 when count reaches threshold
tx_data18_to_response_data1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd36 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd37));

// TX FSM: RESPONSE_CIN goes to NACK when RESPONSE==1 and count reaches threshold
tx_response_cin_to_nack: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1)
    |=> (module_i2c.state_tx == 6'd39));

// TX FSM: RESPONSE_CIN goes to DELAY_BYTES when RESPONSE==0 and count reaches threshold
tx_response_cin_to_delay: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38));

// TX FSM: DELAY_BYTES with count_tx==3 transitions to STOP
tx_delay_bytes_to_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd3)
    |=> (module_i2c.state_tx == 6'd40));

// TX FSM: DELAY_BYTES with count_tx==0 transitions to ADDRESS_1
tx_delay_bytes_to_address1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd0)
    |=> (module_i2c.state_tx == 6'd11));

// TX FSM: DELAY_BYTES with count_tx==1 transitions to DATA0_1
tx_delay_bytes_to_data01: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd1)
    |=> (module_i2c.state_tx == 6'd20));

// TX FSM: DELAY_BYTES with count_tx==2 transitions to DATA1_1
tx_delay_bytes_to_data11: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd2)
    |=> (module_i2c.state_tx == 6'd29));

// RX FSM: CONTROLIN_8 transitions to RESPONSE_CIN when count reaches threshold
rx_ctrl8_to_response_cin: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd9 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd10));

// RX FSM: ADDRESS_8 transitions to RESPONSE_ADDRESS
rx_addr8_to_response_addr: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd18 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd19));

// RX FSM: DATA0_8 transitions to RESPONSE_DATA0_1
rx_data08_to_response_data0: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd27 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd28));

// RX FSM: DATA1_8 transitions to RESPONSE_DATA1_1
rx_data18_to_response_data1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd36 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd37));

// RX FSM: DELAY_BYTES with count_rx==3 transitions to STOP
rx_delay_bytes_to_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd3)
    |=> (module_i2c.state_rx == 6'd40));

// RX FSM: DELAY_BYTES with count_rx==0 transitions to ADDRESS_1
rx_delay_bytes_to_address1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd38 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_rx == 2'd0)
    |=> (module_i2c.state_rx == 6'd11));

// count_timeout increments only in IDLE state with SDA and SCL both 0
count_timeout_increments_in_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx != 6'd0)
    |=> (module_i2c.count_timeout == 12'd0));

// count_timeout is bounded by TIMEOUT_TX or resets
count_timeout_bounded: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.count_timeout <= TIMEOUT_TX));

// fifo_rx_wr_en is 0 in STOP state
fifo_rx_wr_en_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40) |-> (fifo_rx_wr_en == 1'b0));

// TX FSM: START state stays in START while count < threshold
tx_start_stays: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 && module_i2c.count_send_data != DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd1));

// TX FSM: START goes to CONTROLIN_1 after count reaches threshold
tx_start_to_ctrl1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd2));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
