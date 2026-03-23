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
    input SDA,
    input SCL
);

    // TX_EMPTY is always equal to fifo_tx_f_empty
    tx_empty_reflects_fifo_tx_f_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (TX_EMPTY == fifo_tx_f_empty)
    );

    // RX_EMPTY is always equal to fifo_rx_f_empty
    rx_empty_reflects_fifo_rx_f_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (RX_EMPTY == fifo_rx_f_empty)
    );

    // ERROR is asserted when both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are 1
    error_when_both_config_bits_set: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR
    );

    // ERROR is deasserted when not both config bits are set
    no_error_when_config_bits_not_both_set: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> !ERROR
    );

    // On reset, TX state machine goes to IDLE (6'd0)
    reset_tx_state_idle: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == 6'd0)
    );

    // On reset, count_send_data is cleared
    reset_count_send_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0)
    );

    // On reset, fifo_tx_rd_en is deasserted
    reset_fifo_tx_rd_en_low: assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_tx_rd_en
    );

    // On reset, BR_CLK_O is high
    reset_br_clk_o_high: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    // On reset, count_tx is zero
    reset_count_tx_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_tx == 2'd0)
    );

    // On reset, RESPONSE is cleared
    reset_response_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.RESPONSE == 1'b0)
    );

    // On reset, RX state machine goes to IDLE
    reset_rx_state_idle: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == 6'd0)
    );

    // On reset, count_receive_data is cleared
    reset_count_receive_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0)
    );

    // On reset, fifo_rx_wr_en is deasserted
    reset_fifo_rx_wr_en_low: assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_rx_wr_en
    );

    // On reset, BR_CLK_O_RX is low
    reset_br_clk_o_rx_low: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O_RX == 1'b0)
    );

    // On reset, count_timeout is cleared
    reset_count_timeout_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_timeout == 12'd0)
    );

    // TX IDLE: fifo_tx_rd_en is deasserted while in IDLE state
    tx_idle_fifo_rd_en_low: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd0) |=> !fifo_tx_rd_en
    );

    // TX START state: stays in START when count_send_data != DATA_CONFIG_REG[13:2]
    tx_start_stays_when_counter_not_met: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd1) && (module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd1)
    );

    // TX START -> CONTROLIN_1 when counter reached
    tx_start_to_controlin1: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd1) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd2)
    );

    // TX STOP -> IDLE when counter reached
    tx_stop_to_idle: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd40) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd0)
    );

    // TX STOP stays in STOP when counter not met
    tx_stop_stays_when_counter_not_met: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd40) && (module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd40)
    );

    // TX RESPONSE_CIN -> DELAY_BYTES on ACK
    tx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd10) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_CIN -> NACK on NACK
    tx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd10) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX RESPONSE_ADDRESS -> DELAY_BYTES on ACK
    tx_response_address_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd19) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_ADDRESS -> NACK on NACK
    tx_response_address_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd19) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX RESPONSE_DATA0_1 -> DELAY_BYTES on ACK
    tx_response_data0_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd28) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_DATA0_1 -> NACK on NACK
    tx_response_data0_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd28) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX RESPONSE_DATA1_1 -> DELAY_BYTES on ACK
    tx_response_data1_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd37) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_DATA1_1 -> NACK on NACK
    tx_response_data1_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd37) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX DELAY_BYTES -> STOP when count_tx == 3
    tx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd38) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.count_tx == 2'd3) |=> (module_i2c.state_tx == 6'd40)
    );

    // TX DELAY_BYTES -> ADDRESS_1 when count_tx == 0
    tx_delay_bytes_count0_to_address1: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd38) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.count_tx == 2'd0) |=> (module_i2c.state_tx == 6'd11)
    );

    // TX DELAY_BYTES -> DATA0_1 when count_tx == 1
    tx_delay_bytes_count1_to_data0: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd38) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.count_tx == 2'd1) |=> (module_i2c.state_tx == 6'd20)
    );

    // TX DELAY_BYTES -> DATA1_1 when count_tx == 2
    tx_delay_bytes_count2_to_data1: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd38) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.count_tx == 2'd2) |=> (module_i2c.state_tx == 6'd29)
    );

    // fifo_tx_rd_en asserted after RESPONSE_DATA1_1 completes
    tx_rd_en_after_response_data1: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd37) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> fifo_tx_rd_en
    );

    // TX IDLE: does not go to START when DATA_CONFIG_REG[0] is 0
    tx_idle_stays_when_config0_zero: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd0) && (DATA_CONFIG_REG[0] == 1'b0) |=> (module_i2c.state_tx == 6'd0)
    );

    // TX IDLE: does not go to START when error config (both bits set)
    tx_idle_stays_when_error_config: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd0) && (DATA_CONFIG_REG[0] == 1'b1) && (DATA_CONFIG_REG[1] == 1'b1) |=> (module_i2c.state_tx == 6'd0)
    );

    // RX STOP -> IDLE when counter reached
    rx_stop_to_idle: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd40) && (module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_rx == 6'd0)
    );

    // RX STOP: fifo_rx_wr_en is deasserted
    rx_stop_fifo_wr_en_low: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd40) |=> !fifo_rx_wr_en
    );

    // ENABLE_SDA is high when RX state is in any response state
    enable_sda_high_when_rx_in_response: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) |-> ENABLE_SDA
    );

    // ENABLE_SDA is low when TX state is in response and RX is not
    enable_sda_low_when_tx_in_response_rx_not: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
                         (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> !ENABLE_SDA
    );

    // ENABLE_SCL is high when RX state is in any response state
    enable_scl_high_when_rx_in_response: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) |-> ENABLE_SCL
    );

    // ENABLE_SCL is high when TX state is in response and RX is not
    enable_scl_high_when_tx_in_response_rx_not: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
                         (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> ENABLE_SCL
    );

    // ENABLE_SCL is low when neither TX nor RX is in a response state
    enable_scl_low_when_no_response_state: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
                        !(module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> !ENABLE_SCL
    );

    // ENABLE_SDA is high when neither TX nor RX is in a response state
    enable_sda_high_when_no_response_state: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
                        !(module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) |-> ENABLE_SDA
    );

    // Timeout counter resets when not in IDLE
    timeout_resets_when_not_idle: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx != 6'd0) |=> (module_i2c.count_timeout == 12'd0)
    );

    // Timeout counter increments in IDLE when SDA and SCL are low and below threshold
    timeout_counter_increments_in_idle: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd0) && (module_i2c.count_timeout <= TIMEOUT_TX) && (SDA == 1'b0) && (SCL == 1'b0) |=> (module_i2c.count_timeout == $past(module_i2c.count_timeout) + 12'd1)
    );

    // TX CONTROLIN_1 stays when counter not met
    tx_controlin1_stays_when_counter_not_met: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd2) && (module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd2)
    );

    // TX CONTROLIN_8 -> RESPONSE_CIN when counter met
    tx_controlin8_to_response_cin: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd9) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd10)
    );

    // TX ADDRESS_8 -> RESPONSE_ADDRESS when counter met
    tx_address8_to_response_address: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd18) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd19)
    );

    // TX DATA0_8 -> RESPONSE_DATA0_1 when counter met
    tx_data0_8_to_response_data0: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd27) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd28)
    );

    // TX DATA1_8 -> RESPONSE_DATA1_1 when counter met
    tx_data1_8_to_response_data1: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd36) && (module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd37)
    );

    // RX RESPONSE_CIN -> DELAY_BYTES on ACK
    rx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd10) && (module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_rx == 6'd38)
    );

    // RX RESPONSE_ADDRESS -> DELAY_BYTES on ACK
    rx_response_address_ack_to_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd19) && (module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) && (module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_rx == 6'd38)
    );

    // RX DELAY_BYTES -> STOP when count_rx == 3
    rx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd38) && (module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) && (module_i2c.count_rx == 2'd3) |=> (module_i2c.state_rx == 6'd40)
    );

    // RX IDLE: does not start when both config bits same direction (no rx mode)
    rx_idle_stays_when_not_rx_mode: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd0) && (DATA_CONFIG_REG[0] == 1'b0) && (DATA_CONFIG_REG[1] == 1'b0) |=> (module_i2c.state_rx == 6'd0)
    );

    // RX IDLE: stays when error config
    rx_idle_stays_when_error_config: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd0) && (DATA_CONFIG_REG[0] == 1'b1) && (DATA_CONFIG_REG[1] == 1'b1) |=> (module_i2c.state_rx == 6'd0)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
