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

    // TX_EMPTY directly mirrors fifo_tx_f_empty
    tx_empty_mirrors_fifo_tx_f_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (TX_EMPTY == fifo_tx_f_empty)
    );

    // RX_EMPTY directly mirrors fifo_rx_f_empty
    rx_empty_mirrors_fifo_rx_f_empty: assert property (
        @(posedge PCLK) 1'b1 |-> (RX_EMPTY == fifo_rx_f_empty)
    );

    // ERROR asserted when both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are 1
    error_asserted_when_both_config_bits_high: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR
    );

    // ERROR deasserted when not both config bits are set
    error_deasserted_when_config_bits_not_both_high: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> !ERROR
    );

    // After reset: state_tx goes to IDLE (6'd0)
    reset_state_tx_to_idle: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_tx == 6'd0)
    );

    // After reset: state_rx goes to IDLE (6'd0)
    reset_state_rx_to_idle: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_rx == 6'd0)
    );

    // After reset: fifo_tx_rd_en is 0
    reset_fifo_tx_rd_en_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_tx_rd_en == 1'b0)
    );

    // After reset: fifo_rx_wr_en is 0
    reset_fifo_rx_wr_en_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_rx_wr_en == 1'b0)
    );

    // After reset: count_send_data is 0
    reset_count_send_data_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_send_data == 12'd0)
    );

    // After reset: count_receive_data is 0
    reset_count_receive_data_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_receive_data == 12'd0)
    );

    // After reset: count_tx is 0
    reset_count_tx_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_tx == 2'd0)
    );

    // After reset: count_rx is 0
    reset_count_rx_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_rx == 2'd0)
    );

    // After reset: BR_CLK_O is 1
    reset_br_clk_o_high: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    // After reset: BR_CLK_O_RX is 0
    reset_br_clk_o_rx_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O_RX == 1'b0)
    );

    // After reset: RESPONSE is 0
    reset_response_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.RESPONSE == 1'b0)
    );

    // After reset: SDA_OUT is 1
    reset_sda_out_high: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.SDA_OUT == 1'b1)
    );

    // After reset: SDA_OUT_RX is 0
    reset_sda_out_rx_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.SDA_OUT_RX == 1'b0)
    );

    // After reset: count_timeout is 0
    reset_count_timeout_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_timeout == 12'd0)
    );

    // SCL driven by BR_CLK_O when DATA_CONFIG_REG[0]=1 and DATA_CONFIG_REG[1]=0
    scl_equals_br_clk_o_in_tx_mode: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> (SCL === module_i2c.BR_CLK_O)
    );

    // SCL driven by BR_CLK_O_RX otherwise
    scl_equals_br_clk_o_rx_in_rx_mode: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> (SCL === module_i2c.BR_CLK_O_RX)
    );

    // IDLE TX: fifo_tx_rd_en is 0 while in IDLE
    idle_tx_fifo_tx_rd_en_zero: assert property (
        @(posedge PCLK) (PRESETn && module_i2c.state_tx == 6'd0) |=> (fifo_tx_rd_en == 1'b0)
    );

    // TX IDLE -> START when conditions met
    tx_idle_transitions_to_start: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd0 &&
                         DATA_CONFIG_REG[0] == 1'b1 &&
                         DATA_CONFIG_REG[1] == 1'b0 &&
                         ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
                         module_i2c.count_timeout < TIMEOUT_TX) |=> (module_i2c.state_tx == 6'd1)
    );

    // TX IDLE stays IDLE when DATA_CONFIG_REG[0]=0
    tx_idle_stays_idle_when_disabled: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd0 &&
                         DATA_CONFIG_REG[0] == 1'b0 &&
                         DATA_CONFIG_REG[1] == 1'b0) |=> (module_i2c.state_tx == 6'd0)
    );

    // TX IDLE stays IDLE when error condition (both bits set)
    tx_idle_stays_idle_on_error: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd0 &&
                         DATA_CONFIG_REG[0] == 1'b1 &&
                         DATA_CONFIG_REG[1] == 1'b1) |=> (module_i2c.state_tx == 6'd0)
    );

    // TX START stays in START while counter not reached
    tx_start_stays_while_counting: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd1 &&
                         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd1)
    );

    // TX START -> CONTROLIN_1 when counter reached
    tx_start_to_controlin1_when_count_reached: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd1 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd2)
    );

    // TX STOP -> IDLE when count reached
    tx_stop_to_idle_when_count_reached: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd40 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd0)
    );

    // TX STOP stays in STOP while counting
    tx_stop_stays_while_counting: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd40 &&
                         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd40)
    );

    // TX STOP: BR_CLK_O is set to 1
    tx_stop_br_clk_o_high: assert property (
        @(posedge PCLK) (PRESETn && module_i2c.state_tx == 6'd40) |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    // TX RESPONSE_CIN ACK -> DELAY_BYTES
    tx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd10 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_CIN NACK -> NACK
    tx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd10 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX RESPONSE_ADDRESS ACK -> DELAY_BYTES
    tx_response_address_ack_to_delay_bytes: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd19 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_ADDRESS NACK -> NACK
    tx_response_address_nack_to_nack: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd19 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_tx == 6'd39)
    );

    // TX RESPONSE_DATA0_1 ACK -> DELAY_BYTES
    tx_response_data0_ack_to_delay_bytes: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd28 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_DATA1_1 ACK -> DELAY_BYTES
    tx_response_data1_ack_to_delay_bytes: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd37 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX RESPONSE_DATA1_1: fifo_tx_rd_en asserted when count reaches limit
    tx_rd_en_asserted_at_response_data1_end: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd37 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=> (fifo_tx_rd_en == 1'b1)
    );

    // TX DELAY_BYTES: fifo_tx_rd_en cleared
    tx_delay_bytes_clears_rd_en: assert property (
        @(posedge PCLK) (PRESETn && module_i2c.state_tx == 6'd38) |=> (fifo_tx_rd_en == 1'b0)
    );

    // TX DELAY_BYTES stays while counting
    tx_delay_bytes_stays_while_counting: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd38 &&
                         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_tx == 6'd38)
    );

    // TX DELAY_BYTES -> ADDRESS_1 when count_tx==0 and count reached
    tx_delay_bytes_to_address1_when_count_tx_zero: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd38 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_tx == 2'd0) |=> (module_i2c.state_tx == 6'd11)
    );

    // TX DELAY_BYTES -> DATA0_1 when count_tx==1 and count reached
    tx_delay_bytes_to_data0_when_count_tx_one: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd38 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_tx == 2'd1) |=> (module_i2c.state_tx == 6'd20)
    );

    // TX DELAY_BYTES -> DATA1_1 when count_tx==2 and count reached
    tx_delay_bytes_to_data1_when_count_tx_two: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd38 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_tx == 2'd2) |=> (module_i2c.state_tx == 6'd29)
    );

    // TX DELAY_BYTES -> STOP when count_tx==3 and count reached
    tx_delay_bytes_to_stop_when_count_tx_three: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd38 &&
                         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_tx == 2'd3) |=> (module_i2c.state_tx == 6'd40)
    );

    // count_timeout resets when state_tx is not IDLE
    count_timeout_resets_when_not_idle: assert property (
        @(posedge PCLK) (PRESETn && module_i2c.state_tx != 6'd0) |=> (module_i2c.count_timeout == 12'd0)
    );

    // count_timeout resets when it exceeds TIMEOUT_TX while in IDLE
    count_timeout_resets_when_exceeded: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_tx == 6'd0 &&
                         module_i2c.count_timeout > TIMEOUT_TX) |=> (module_i2c.count_timeout == 12'd0)
    );

    // ENABLE_SDA high when rx state is in a response state
    enable_sda_high_in_rx_response_states: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd10 ||
                         module_i2c.state_rx == 6'd19 ||
                         module_i2c.state_rx == 6'd28 ||
                         module_i2c.state_rx == 6'd37) |-> ENABLE_SDA
    );

    // ENABLE_SDA low when tx is in response state (and rx is not)
    enable_sda_low_when_tx_in_response_not_rx: assert property (
        @(posedge PCLK) (!(module_i2c.state_rx == 6'd10 ||
                           module_i2c.state_rx == 6'd19 ||
                           module_i2c.state_rx == 6'd28 ||
                           module_i2c.state_rx == 6'd37) &&
                         (module_i2c.state_tx == 6'd10 ||
                          module_i2c.state_tx == 6'd19 ||
                          module_i2c.state_tx == 6'd28 ||
                          module_i2c.state_tx == 6'd37)) |-> !ENABLE_SDA
    );

    // ENABLE_SCL high when rx state is in a response state
    enable_scl_high_in_rx_response_states: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd10 ||
                         module_i2c.state_rx == 6'd19 ||
                         module_i2c.state_rx == 6'd28 ||
                         module_i2c.state_rx == 6'd37) |-> ENABLE_SCL
    );

    // ENABLE_SCL high when tx state is in a response state
    enable_scl_high_in_tx_response_states: assert property (
        @(posedge PCLK) (module_i2c.state_tx == 6'd10 ||
                         module_i2c.state_tx == 6'd19 ||
                         module_i2c.state_tx == 6'd28 ||
                         module_i2c.state_tx == 6'd37) |-> ENABLE_SCL
    );

    // ENABLE_SCL low when neither rx nor tx is in response state
    enable_scl_low_when_no_response_states: assert property (
        @(posedge PCLK) (!(module_i2c.state_rx == 6'd10 ||
                           module_i2c.state_rx == 6'd19 ||
                           module_i2c.state_rx == 6'd28 ||
                           module_i2c.state_rx == 6'd37 ||
                           module_i2c.state_tx == 6'd10 ||
                           module_i2c.state_tx == 6'd19 ||
                           module_i2c.state_tx == 6'd28 ||
                           module_i2c.state_tx == 6'd37)) |-> !ENABLE_SCL
    );

    // RX IDLE stays IDLE when DATA_CONFIG_REG[0]=0 and DATA_CONFIG_REG[1]=0
    rx_idle_stays_idle_when_both_config_zero: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd0 &&
                         DATA_CONFIG_REG[0] == 1'b0 &&
                         DATA_CONFIG_REG[1] == 1'b0) |=> (module_i2c.state_rx == 6'd0)
    );

    // RX IDLE stays IDLE on error (both config bits set)
    rx_idle_stays_idle_on_error: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd0 &&
                         DATA_CONFIG_REG[0] == 1'b1 &&
                         DATA_CONFIG_REG[1] == 1'b1) |=> (module_i2c.state_rx == 6'd0)
    );

    // RX STOP -> IDLE when count reached
    rx_stop_to_idle_when_count_reached: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd40 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=> (module_i2c.state_rx == 6'd0)
    );

    // RX STOP: fifo_rx_wr_en cleared
    rx_stop_clears_fifo_rx_wr_en: assert property (
        @(posedge PCLK) (PRESETn && module_i2c.state_rx == 6'd40) |=> (fifo_rx_wr_en == 1'b0)
    );

    // RX RESPONSE_CIN ACK -> DELAY_BYTES
    rx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd10 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b0) |=> (module_i2c.state_rx == 6'd38)
    );

    // RX RESPONSE_CIN NACK -> NACK
    rx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd10 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.RESPONSE == 1'b1) |=> (module_i2c.state_rx == 6'd39)
    );

    // RX DELAY_BYTES -> ADDRESS_1 when count_rx==0 and count reached
    rx_delay_bytes_to_address1_when_count_rx_zero: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd38 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_rx == 2'd0) |=> (module_i2c.state_rx == 6'd11)
    );

    // RX DELAY_BYTES -> DATA0_1 when count_rx==1 and count reached
    rx_delay_bytes_to_data0_when_count_rx_one: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd38 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_rx == 2'd1) |=> (module_i2c.state_rx == 6'd20)
    );

    // RX DELAY_BYTES -> DATA1_1 when count_rx==2 and count reached
    rx_delay_bytes_to_data1_when_count_rx_two: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd38 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_rx == 2'd2) |=> (module_i2c.state_rx == 6'd29)
    );

    // RX DELAY_BYTES -> STOP when count_rx==3 and count reached
    rx_delay_bytes_to_stop_when_count_rx_three: assert property (
        @(posedge PCLK) (PRESETn &&
                         module_i2c.state_rx == 6'd38 &&
                         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
                         module_i2c.count_rx == 2'd3) |=> (module_i2c.state_rx == 6'd40)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
