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
    inout SDA,
    inout SCL
);

// TX_EMPTY directly reflects fifo_tx_f_empty
tx_empty_reflects_fifo_empty: assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

// RX_EMPTY directly reflects fifo_rx_f_empty
rx_empty_reflects_fifo_empty: assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

// ERROR is asserted when both config bits are 1
error_asserted_when_config_11: assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b1);

// ERROR is deasserted when config bits are not both 1
error_deasserted_otherwise: assert property (@(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b0);

// After reset deasserted, TX state machine is IDLE
reset_tx_state_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_tx == 6'd0);

// After reset deasserted, RX state machine is IDLE
reset_rx_state_idle: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.state_rx == 6'd0);

// After reset, count_send_data is 0
reset_count_send_data_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_send_data == 12'd0);

// After reset, count_receive_data is 0
reset_count_receive_data_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_receive_data == 12'd0);

// After reset, fifo_tx_rd_en is 0
reset_fifo_tx_rd_en_low: assert property (@(posedge PCLK) !PRESETn |=> fifo_tx_rd_en == 1'b0);

// After reset, fifo_rx_wr_en is 0
reset_fifo_rx_wr_en_low: assert property (@(posedge PCLK) !PRESETn |=> fifo_rx_wr_en == 1'b0);

// After reset, BR_CLK_O is 1
reset_br_clk_o_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O == 1'b1);

// After reset, SDA_OUT is 1
reset_sda_out_high: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT == 1'b1);

// After reset, count_tx is 0
reset_count_tx_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_tx == 2'd0);

// After reset, count_rx is 0
reset_count_rx_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_rx == 2'd0);

// After reset, count_timeout is 0
reset_count_timeout_zero: assert property (@(posedge PCLK) !PRESETn |=> module_i2c.count_timeout == 12'd0);

// TX state machine stays within valid state range (0-40)
tx_state_valid_range: assert property (@(posedge PCLK) module_i2c.state_tx <= 6'd40);

// RX state machine stays within valid state range (0-40)
rx_state_valid_range: assert property (@(posedge PCLK) module_i2c.state_rx <= 6'd40);

// count_tx stays within 0-3
count_tx_in_range: assert property (@(posedge PCLK) module_i2c.count_tx <= 2'd3);

// count_rx stays within 0-3
count_rx_in_range: assert property (@(posedge PCLK) module_i2c.count_rx <= 2'd3);

// ENABLE_SDA is 1 when RX is in RESPONSE_CIN state
enable_sda_rx_response_cin: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd10) |-> ENABLE_SDA == 1'b1);

// ENABLE_SDA is 1 when RX is in RESPONSE_ADDRESS state
enable_sda_rx_response_address: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd19) |-> ENABLE_SDA == 1'b1);

// ENABLE_SDA is 1 when RX is in RESPONSE_DATA0_1 state
enable_sda_rx_response_data0: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd28) |-> ENABLE_SDA == 1'b1);

// ENABLE_SDA is 1 when RX is in RESPONSE_DATA1_1 state
enable_sda_rx_response_data1: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd37) |-> ENABLE_SDA == 1'b1);

// ENABLE_SCL is 1 when RX is in RESPONSE_CIN state
enable_scl_rx_response_cin: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd10) |-> ENABLE_SCL == 1'b1);

// ENABLE_SCL is 1 when RX is in RESPONSE_ADDRESS state
enable_scl_rx_response_address: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd19) |-> ENABLE_SCL == 1'b1);

// ENABLE_SCL is 1 when RX is in RESPONSE_DATA0_1 state
enable_scl_rx_response_data0: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd28) |-> ENABLE_SCL == 1'b1);

// ENABLE_SCL is 1 when RX is in RESPONSE_DATA1_1 state
enable_scl_rx_response_data1: assert property (@(posedge PCLK) (module_i2c.state_rx == 6'd37) |-> ENABLE_SCL == 1'b1);

// ENABLE_SDA is 0 when TX is in response state and RX is not in any response state
enable_sda_low_tx_response_only: assert property (@(posedge PCLK)
    (module_i2c.state_rx != 6'd10 && module_i2c.state_rx != 6'd19 &&
     module_i2c.state_rx != 6'd28 && module_i2c.state_rx != 6'd37) &&
    (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
     module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> ENABLE_SDA == 1'b0);

// ENABLE_SCL is 1 when TX is in response state and RX is not in any response state
enable_scl_high_tx_response_only: assert property (@(posedge PCLK)
    (module_i2c.state_rx != 6'd10 && module_i2c.state_rx != 6'd19 &&
     module_i2c.state_rx != 6'd28 && module_i2c.state_rx != 6'd37) &&
    (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
     module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> ENABLE_SCL == 1'b1);

// SCL is driven by BR_CLK_O in TX mode (when DATA_CONFIG_REG[0]=1, DATA_CONFIG_REG[1]=0)
scl_driven_by_br_clk_o_in_tx_mode: assert property (@(posedge PCLK)
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> SCL == module_i2c.BR_CLK_O);

// SCL is driven by BR_CLK_O_RX in RX mode (when DATA_CONFIG_REG[0]=1 is not true or DATA_CONFIG_REG[1]=1)
scl_driven_by_br_clk_o_rx_otherwise: assert property (@(posedge PCLK)
    !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> SCL == module_i2c.BR_CLK_O_RX);

// When TX is in IDLE state, fifo_tx_rd_en becomes 0 on next cycle
fifo_tx_rd_en_low_after_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0) |=> fifo_tx_rd_en == 1'b0);

// STOP state in TX transitions to IDLE when count matches
tx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd40 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd0);

// START TX state transitions to CONTROLIN_1 when count reaches limit
tx_start_to_controlin1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd2);

// IDLE TX transitions to START when conditions met
tx_idle_to_start_when_enabled: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 &&
     ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
     DATA_CONFIG_REG[1] == 1'b0 &&
     module_i2c.count_timeout < TIMEOUT_TX) |=> module_i2c.state_tx == 6'd1);

// fifo_tx_rd_en is asserted cycle after RESPONSE_DATA1_1 completes count
rd_en_set_after_response_data1_completes: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd37 && module_i2c.count_send_data >= DATA_CONFIG_REG[13:2]) |=> fifo_tx_rd_en == 1'b1);

// count_timeout resets when TX is not in IDLE state
count_timeout_resets_when_tx_not_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx != 6'd0) |=> module_i2c.count_timeout == 12'd0);

// STOP TX state stays in STOP while count has not reached limit
tx_stop_stays_until_count_done: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd40 && module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd40);

// STOP RX state transitions to IDLE when count reaches limit
rx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_rx == 6'd0);

// fifo_rx_wr_en is 0 in RX STOP state
fifo_rx_wr_en_low_in_rx_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == 6'd40) |=> fifo_rx_wr_en == 1'b0);

// TX CONTROLIN_8 transitions to RESPONSE_CIN when count matches
tx_controlin8_to_response_cin: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd9 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd10);

// TX ADDRESS_8 transitions to RESPONSE_ADDRESS when count matches
tx_address8_to_response_address: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd18 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd19);

// TX DATA0_8 transitions to RESPONSE_DATA0_1 when count matches
tx_data0_8_to_response_data0: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd27 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd28);

// TX DATA1_8 transitions to RESPONSE_DATA1_1 when count matches
tx_data1_8_to_response_data1: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd36 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> module_i2c.state_tx == 6'd37);

// TX RESPONSE_CIN transitions to DELAY_BYTES on ACK
tx_response_cin_ack_to_delay: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=> module_i2c.state_tx == 6'd38);

// TX RESPONSE_CIN transitions to NACK on NACK response
tx_response_cin_nack_to_nack: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd10 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1) |=> module_i2c.state_tx == 6'd39);

// TX DELAY_BYTES sets count_tx to 0 when stop condition
tx_delay_bytes_count3_to_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd38 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd3) |=> module_i2c.state_tx == 6'd40);

// TX IDLE stays in IDLE when both config bits are 0 and data is available
tx_idle_stays_when_disabled: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] == 1'b0 &&
     (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b0) |=> module_i2c.state_tx == 6'd0);

// TX IDLE stays in IDLE when error condition (both config bits set)
tx_idle_stays_on_error: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] == 1'b1 &&
     (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b1) |=> module_i2c.state_tx == 6'd0);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
