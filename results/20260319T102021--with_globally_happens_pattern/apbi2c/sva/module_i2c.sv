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
    tx_empty_when_fifo_tx_empty: assert property (
        @(posedge PCLK) fifo_tx_f_empty |-> TX_EMPTY
    );

    tx_not_empty_when_fifo_tx_not_empty: assert property (
        @(posedge PCLK) !fifo_tx_f_empty |-> !TX_EMPTY
    );

    // RX_EMPTY directly mirrors fifo_rx_f_empty
    rx_empty_when_fifo_rx_empty: assert property (
        @(posedge PCLK) fifo_rx_f_empty |-> RX_EMPTY
    );

    rx_not_empty_when_fifo_rx_not_empty: assert property (
        @(posedge PCLK) !fifo_rx_f_empty |-> !RX_EMPTY
    );

    // ERROR asserted only when both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are set
    error_when_both_config_bits_set: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> ERROR
    );

    no_error_unless_both_config_bits_set: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> !ERROR
    );

    // SCL follows BR_CLK_O when in TX master mode (config[0]=1, config[1]=0)
    scl_follows_br_clk_o_in_tx_mode: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |-> (SCL == module_i2c.BR_CLK_O)
    );

    // SCL follows BR_CLK_O_RX otherwise
    scl_follows_br_clk_o_rx_otherwise: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |-> (SCL == module_i2c.BR_CLK_O_RX)
    );

    // ENABLE_SDA is high when RX FSM is in any RESPONSE state
    enable_sda_high_rx_response_cin: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd10) |-> ENABLE_SDA
    );

    enable_sda_high_rx_response_address: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd19) |-> ENABLE_SDA
    );

    enable_sda_high_rx_response_data0: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd28) |-> ENABLE_SDA
    );

    enable_sda_high_rx_response_data1: assert property (
        @(posedge PCLK) (module_i2c.state_rx == 6'd37) |-> ENABLE_SDA
    );

    // ENABLE_SDA is low when TX FSM is in RESPONSE state and RX FSM is not
    enable_sda_low_tx_response_cin_not_rx: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd10) &&
        !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
          module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
        |-> !ENABLE_SDA
    );

    enable_sda_low_tx_response_addr_not_rx: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd19) &&
        !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
          module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
        |-> !ENABLE_SDA
    );

    enable_sda_low_tx_response_data0_not_rx: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd28) &&
        !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
          module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
        |-> !ENABLE_SDA
    );

    enable_sda_low_tx_response_data1_not_rx: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd37) &&
        !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
          module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
        |-> !ENABLE_SDA
    );

    // ENABLE_SCL is high when RX FSM is in any RESPONSE state
    enable_scl_high_rx_response: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
         module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
        |-> ENABLE_SCL
    );

    // ENABLE_SCL is high when TX FSM is in any RESPONSE state
    enable_scl_high_tx_response: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
         module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37)
        |-> ENABLE_SCL
    );

    // ENABLE_SCL is low when neither FSM is in a RESPONSE state
    enable_scl_low_when_no_response_state: assert property (
        @(posedge PCLK)
        !(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
          module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
        !(module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
          module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37)
        |-> !ENABLE_SCL
    );

    // TX FSM: STOP -> IDLE when count reached
    tx_stop_to_idle_on_count_match: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd40 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd0)
    );

    // TX FSM: STOP stays in STOP when count not reached
    tx_stop_stays_stop: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd40 && module_i2c.count_send_data != DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd40)
    );

    // TX FSM: RESPONSE_CIN + ACK -> DELAY_BYTES
    tx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd10 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_tx == 6'd38)
    );

    // TX FSM: RESPONSE_CIN + NACK -> NACK state
    tx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd10 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_tx == 6'd39)
    );

    // TX FSM: RESPONSE_ADDRESS + ACK -> DELAY_BYTES
    tx_response_address_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd19 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_tx == 6'd38)
    );

    // TX FSM: RESPONSE_ADDRESS + NACK -> NACK state
    tx_response_address_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd19 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_tx == 6'd39)
    );

    // TX FSM: RESPONSE_DATA0_1 + ACK -> DELAY_BYTES
    tx_response_data0_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd28 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_tx == 6'd38)
    );

    // TX FSM: RESPONSE_DATA0_1 + NACK -> NACK state
    tx_response_data0_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd28 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_tx == 6'd39)
    );

    // TX FSM: RESPONSE_DATA1_1 + ACK -> DELAY_BYTES
    tx_response_data1_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd37 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_tx == 6'd38)
    );

    // TX FSM: RESPONSE_DATA1_1 + NACK -> NACK state
    tx_response_data1_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd37 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_tx == 6'd39)
    );

    // TX FSM: DELAY_BYTES -> ADDRESS_1 when count_tx == 0
    tx_delay_bytes_to_address1_count0: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd38 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd0)
        |-> (module_i2c.next_state_tx == 6'd11)
    );

    // TX FSM: DELAY_BYTES -> DATA0_1 when count_tx == 1
    tx_delay_bytes_to_data0_count1: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd38 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd1)
        |-> (module_i2c.next_state_tx == 6'd20)
    );

    // TX FSM: DELAY_BYTES -> DATA1_1 when count_tx == 2
    tx_delay_bytes_to_data1_count2: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd38 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd2)
        |-> (module_i2c.next_state_tx == 6'd29)
    );

    // TX FSM: DELAY_BYTES -> STOP when count_tx == 3
    tx_delay_bytes_to_stop_count3: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd38 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd3)
        |-> (module_i2c.next_state_tx == 6'd40)
    );

    // TX FSM: START -> CONTROLIN_1 when count reached
    tx_start_to_controlin1_on_count_match: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd2)
    );

    // TX FSM: IDLE stays in IDLE when config[0]=0 and config[1]=0 with fifo conditions
    tx_idle_stays_idle_config0_zero: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd0 && !DATA_CONFIG_REG[0] &&
         (fifo_tx_f_full || !fifo_tx_f_empty) && !DATA_CONFIG_REG[1])
        |-> (module_i2c.next_state_tx == 6'd0)
    );

    // TX FSM: IDLE stays in IDLE when config[0]=1 and config[1]=1
    tx_idle_stays_idle_error_mode: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] &&
         (fifo_tx_f_full || !fifo_tx_f_empty) && DATA_CONFIG_REG[1])
        |-> (module_i2c.next_state_tx == 6'd0)
    );

    // TX FSM: IDLE -> START when TX mode enabled with data and timeout not expired
    tx_idle_to_start_when_tx_enabled: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd0 && DATA_CONFIG_REG[0] &&
         ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
         !DATA_CONFIG_REG[1] && module_i2c.count_timeout < TIMEOUT_TX)
        |-> (module_i2c.next_state_tx == 6'd1)
    );

    // RX FSM: STOP -> IDLE when count reached
    rx_stop_to_idle_on_count_match: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd40 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd0)
    );

    // RX FSM: STOP stays in STOP when count not reached
    rx_stop_stays_stop: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd40 && module_i2c.count_receive_data != DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd40)
    );

    // RX FSM: RESPONSE_CIN + ACK -> DELAY_BYTES
    rx_response_cin_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd10 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_rx == 6'd38)
    );

    // RX FSM: RESPONSE_CIN + NACK -> NACK
    rx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd10 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_rx == 6'd39)
    );

    // RX FSM: RESPONSE_ADDRESS + ACK -> DELAY_BYTES
    rx_response_address_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd19 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_rx == 6'd38)
    );

    // RX FSM: RESPONSE_ADDRESS + NACK -> NACK
    rx_response_address_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd19 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_rx == 6'd39)
    );

    // RX FSM: RESPONSE_DATA0_1 + ACK -> DELAY_BYTES
    rx_response_data0_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd28 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0)
        |-> (module_i2c.next_state_rx == 6'd38)
    );

    // RX FSM: RESPONSE_DATA0_1 + NACK -> NACK
    rx_response_data0_nack_to_nack: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd28 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_rx == 6'd39)
    );

    // RX FSM: RESPONSE_DATA1_1 + ACK -> DELAY_BYTES
    rx_response_data1_ack_to_delay_bytes: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd37 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1)
        |-> (module_i2c.next_state_rx == 6'd39)
    );

    // RX FSM: DELAY_BYTES -> ADDRESS_1 when count_rx == 0
    rx_delay_bytes_to_address1_count0: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd38 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd0)
        |-> (module_i2c.next_state_rx == 6'd11)
    );

    // RX FSM: DELAY_BYTES -> DATA0_1 when count_rx == 1
    rx_delay_bytes_to_data0_count1: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd38 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd1)
        |-> (module_i2c.next_state_rx == 6'd20)
    );

    // RX FSM: DELAY_BYTES -> DATA1_1 when count_rx == 2
    rx_delay_bytes_to_data1_count2: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd38 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd2)
        |-> (module_i2c.next_state_rx == 6'd29)
    );

    // RX FSM: DELAY_BYTES -> STOP when count_rx == 3
    rx_delay_bytes_to_stop_count3: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd38 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd3)
        |-> (module_i2c.next_state_rx == 6'd40)
    );

    // RX FSM IDLE: stays IDLE when config[0]=0 and config[1]=0
    rx_idle_stays_idle_config0_zero: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd0 && !DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1])
        |-> (module_i2c.next_state_rx == 6'd0)
    );

    // RX FSM IDLE: stays IDLE when config[0]=1 and config[1]=1
    rx_idle_stays_idle_error_mode: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd0 && DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1])
        |-> (module_i2c.next_state_rx == 6'd0)
    );

    // Synchronous reset: TX FSM goes to IDLE next cycle
    reset_tx_state_to_idle: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == 6'd0)
    );

    // Synchronous reset: RX FSM goes to IDLE next cycle
    reset_rx_state_to_idle: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == 6'd0)
    );

    // Synchronous reset: fifo_tx_rd_en deasserted next cycle
    reset_fifo_tx_rd_en_deasserted: assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_tx_rd_en
    );

    // Synchronous reset: fifo_rx_wr_en deasserted next cycle
    reset_fifo_rx_wr_en_deasserted: assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_rx_wr_en
    );

    // Synchronous reset: count_send_data cleared next cycle
    reset_count_send_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0)
    );

    // Synchronous reset: count_receive_data cleared next cycle
    reset_count_receive_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0)
    );

    // Synchronous reset: count_timeout cleared next cycle
    reset_count_timeout_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_timeout == 12'd0)
    );

    // Synchronous reset: count_tx cleared next cycle
    reset_count_tx_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_tx == 2'd0)
    );

    // Synchronous reset: count_rx cleared next cycle
    reset_count_rx_zero: assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_rx == 2'd0)
    );

    // count_timeout only increments in IDLE state; resets otherwise (next cycle)
    count_timeout_reset_when_not_idle: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx != 6'd0) |=> (module_i2c.count_timeout == 12'd0)
    );

    // count_timeout resets when exceeded TIMEOUT_TX (next cycle)
    count_timeout_reset_when_exceeded: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.count_timeout > TIMEOUT_TX) |=> (module_i2c.count_timeout == 12'd0)
    );

    // fifo_tx_rd_en asserted only at end of RESPONSE_DATA1_1 in TX FSM
    tx_rd_en_only_in_response_data1: assert property (
        @(posedge PCLK) PRESETn && fifo_tx_rd_en |-> (module_i2c.state_tx == 6'd37)
    );

    // fifo_tx_rd_en is deasserted in IDLE state
    tx_idle_rd_en_deasserted: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_tx == 6'd0) |-> !fifo_tx_rd_en
    );

    // fifo_rx_wr_en deasserted in STOP state (next cycle)
    rx_wr_en_deasserted_in_stop: assert property (
        @(posedge PCLK) PRESETn && (module_i2c.state_rx == 6'd40) |=> !fifo_rx_wr_en
    );

    // TX FSM consecutive state transitions via count: e.g. CONTROLIN_1 -> CONTROLIN_2
    tx_controlin1_to_controlin2_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd3)
    );

    tx_controlin2_to_controlin3_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd3 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd4)
    );

    tx_controlin8_to_response_cin_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd9 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd10)
    );

    tx_address8_to_response_address_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd18 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd19)
    );

    tx_data0_8_to_response_data0_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd27 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd28)
    );

    tx_data1_8_to_response_data1_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_tx == 6'd36 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_tx == 6'd37)
    );

    // RX FSM: CONTROLIN_8 -> RESPONSE_CIN on count match
    rx_controlin8_to_response_cin_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd9 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd10)
    );

    // RX FSM: ADDRESS_8 -> RESPONSE_ADDRESS on count match
    rx_address8_to_response_address_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd18 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd19)
    );

    // RX FSM: DATA0_8 -> RESPONSE_DATA0_1 on count match
    rx_data0_8_to_response_data0_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd27 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd28)
    );

    // RX FSM: DATA1_8 -> RESPONSE_DATA1_1 on count match
    rx_data1_8_to_response_data1_on_count: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == 6'd36 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |-> (module_i2c.next_state_rx == 6'd37)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
