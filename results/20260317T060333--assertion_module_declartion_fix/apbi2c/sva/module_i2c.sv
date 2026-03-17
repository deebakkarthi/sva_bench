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

    localparam [5:0] ST_IDLE          = 6'd0;
    localparam [5:0] ST_START         = 6'd1;
    localparam [5:0] ST_CONTROLIN_1   = 6'd2;
    localparam [5:0] ST_CONTROLIN_2   = 6'd3;
    localparam [5:0] ST_CONTROLIN_3   = 6'd4;
    localparam [5:0] ST_CONTROLIN_4   = 6'd5;
    localparam [5:0] ST_CONTROLIN_5   = 6'd6;
    localparam [5:0] ST_CONTROLIN_6   = 6'd7;
    localparam [5:0] ST_CONTROLIN_7   = 6'd8;
    localparam [5:0] ST_CONTROLIN_8   = 6'd9;
    localparam [5:0] ST_RESPONSE_CIN  = 6'd10;
    localparam [5:0] ST_ADDRESS_1     = 6'd11;
    localparam [5:0] ST_ADDRESS_2     = 6'd12;
    localparam [5:0] ST_ADDRESS_3     = 6'd13;
    localparam [5:0] ST_ADDRESS_4     = 6'd14;
    localparam [5:0] ST_ADDRESS_5     = 6'd15;
    localparam [5:0] ST_ADDRESS_6     = 6'd16;
    localparam [5:0] ST_ADDRESS_7     = 6'd17;
    localparam [5:0] ST_ADDRESS_8     = 6'd18;
    localparam [5:0] ST_RESPONSE_ADDR = 6'd19;
    localparam [5:0] ST_DATA0_1       = 6'd20;
    localparam [5:0] ST_DATA0_2       = 6'd21;
    localparam [5:0] ST_DATA0_3       = 6'd22;
    localparam [5:0] ST_DATA0_4       = 6'd23;
    localparam [5:0] ST_DATA0_5       = 6'd24;
    localparam [5:0] ST_DATA0_6       = 6'd25;
    localparam [5:0] ST_DATA0_7       = 6'd26;
    localparam [5:0] ST_DATA0_8       = 6'd27;
    localparam [5:0] ST_RESP_DATA0    = 6'd28;
    localparam [5:0] ST_DATA1_1       = 6'd29;
    localparam [5:0] ST_DATA1_2       = 6'd30;
    localparam [5:0] ST_DATA1_3       = 6'd31;
    localparam [5:0] ST_DATA1_4       = 6'd32;
    localparam [5:0] ST_DATA1_5       = 6'd33;
    localparam [5:0] ST_DATA1_6       = 6'd34;
    localparam [5:0] ST_DATA1_7       = 6'd35;
    localparam [5:0] ST_DATA1_8       = 6'd36;
    localparam [5:0] ST_RESP_DATA1    = 6'd37;
    localparam [5:0] ST_DELAY_BYTES   = 6'd38;
    localparam [5:0] ST_NACK          = 6'd39;
    localparam [5:0] ST_STOP          = 6'd40;

    // -----------------------------------------------------------------------
    // Reset behaviour
    // -----------------------------------------------------------------------

    reset_tx_state_goes_idle: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.state_tx == ST_IDLE
    );

    reset_rx_state_goes_idle: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.state_rx == ST_IDLE
    );

    reset_count_send_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.count_send_data == 12'd0
    );

    reset_count_receive_data_zero: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.count_receive_data == 12'd0
    );

    reset_count_timeout_zero: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.count_timeout == 12'd0
    );

    reset_fifo_tx_rd_en_deasserted: assert property (
        @(posedge PCLK) !PRESETn |=> fifo_tx_rd_en == 1'b0
    );

    reset_fifo_rx_wr_en_deasserted: assert property (
        @(posedge PCLK) !PRESETn |=> fifo_rx_wr_en == 1'b0
    );

    reset_count_tx_zero: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.count_tx == 2'd0
    );

    reset_count_rx_zero: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.count_rx == 2'd0
    );

    reset_br_clk_o_high: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O == 1'b1
    );

    reset_br_clk_o_rx_low: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.BR_CLK_O_RX == 1'b0
    );

    reset_sda_out_high: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT == 1'b1
    );

    reset_sda_out_rx_low: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.SDA_OUT_RX == 1'b0
    );

    reset_response_low: assert property (
        @(posedge PCLK) !PRESETn |=> module_i2c.RESPONSE == 1'b0
    );

    // -----------------------------------------------------------------------
    // Combinational output correctness
    // -----------------------------------------------------------------------

    tx_empty_mirrors_fifo_empty: assert property (
        @(posedge PCLK) TX_EMPTY == fifo_tx_f_empty
    );

    rx_empty_mirrors_fifo_empty: assert property (
        @(posedge PCLK) RX_EMPTY == fifo_rx_f_empty
    );

    error_when_both_config_bits_set: assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b1
    );

    no_error_when_not_both_config_bits: assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b0
    );

    // -----------------------------------------------------------------------
    // State machine valid encoding
    // -----------------------------------------------------------------------

    tx_state_valid_encoding: assert property (
        @(posedge PCLK) module_i2c.state_tx <= 6'd40
    );

    rx_state_valid_encoding: assert property (
        @(posedge PCLK) module_i2c.state_rx <= 6'd40
    );

    // -----------------------------------------------------------------------
    // TX FSM: IDLE stay conditions
    // -----------------------------------------------------------------------

    tx_stays_idle_when_disabled_no_fifo: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_IDLE &&
        DATA_CONFIG_REG[0] == 1'b0 &&
        DATA_CONFIG_REG[1] == 1'b0 &&
        (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0)
        |=> module_i2c.state_tx == ST_IDLE
    );

    tx_stays_idle_when_error_condition: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_IDLE &&
        DATA_CONFIG_REG[0] == 1'b1 &&
        DATA_CONFIG_REG[1] == 1'b1 &&
        (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0)
        |=> module_i2c.state_tx == ST_IDLE
    );

    // -----------------------------------------------------------------------
    // TX FSM: IDLE -> START transition
    // -----------------------------------------------------------------------

    tx_idle_transitions_to_start: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_IDLE &&
        DATA_CONFIG_REG[0] == 1'b1 &&
        DATA_CONFIG_REG[1] == 1'b0 &&
        ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
        module_i2c.count_timeout < TIMEOUT_TX
        |=> module_i2c.state_tx == ST_START
    );

    // -----------------------------------------------------------------------
    // TX FSM: CONTROLIN sequence
    // -----------------------------------------------------------------------

    tx_controlin_1_to_2_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_1 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_2
    );

    tx_controlin_2_to_3_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_2 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_3
    );

    tx_controlin_3_to_4_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_3 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_4
    );

    tx_controlin_4_to_5_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_4 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_5
    );

    tx_controlin_5_to_6_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_5 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_6
    );

    tx_controlin_6_to_7_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_6 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_7
    );

    tx_controlin_7_to_8_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_7 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_CONTROLIN_8
    );

    tx_controlin_8_to_response_cin_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_CONTROLIN_8 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_RESPONSE_CIN
    );

    // -----------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN -> ACK/NACK branch
    // -----------------------------------------------------------------------

    tx_response_cin_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESPONSE_CIN &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_tx == ST_DELAY_BYTES
    );

    tx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESPONSE_CIN &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_tx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // TX FSM: ADDRESS sequence
    // -----------------------------------------------------------------------

    tx_address_1_to_2_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_ADDRESS_1 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_ADDRESS_2
    );

    tx_address_8_to_response_addr_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_ADDRESS_8 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_RESPONSE_ADDR
    );

    tx_response_addr_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESPONSE_ADDR &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_tx == ST_DELAY_BYTES
    );

    tx_response_addr_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESPONSE_ADDR &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_tx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // TX FSM: DATA0 sequence
    // -----------------------------------------------------------------------

    tx_data0_8_to_response_data0_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DATA0_8 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_RESP_DATA0
    );

    tx_response_data0_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESP_DATA0 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_tx == ST_DELAY_BYTES
    );

    tx_response_data0_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESP_DATA0 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_tx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // TX FSM: DATA1 sequence
    // -----------------------------------------------------------------------

    tx_data1_8_to_response_data1_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DATA1_8 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_RESP_DATA1
    );

    tx_response_data1_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESP_DATA1 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_tx == ST_DELAY_BYTES
    );

    tx_response_data1_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESP_DATA1 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_tx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // TX FSM: DELAY_BYTES routing based on count_tx
    // -----------------------------------------------------------------------

    tx_delay_bytes_count0_to_address1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DELAY_BYTES &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_tx == 2'd0
        |=> module_i2c.state_tx == ST_ADDRESS_1
    );

    tx_delay_bytes_count1_to_data0_1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DELAY_BYTES &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_tx == 2'd1
        |=> module_i2c.state_tx == ST_DATA0_1
    );

    tx_delay_bytes_count2_to_data1_1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DELAY_BYTES &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_tx == 2'd2
        |=> module_i2c.state_tx == ST_DATA1_1
    );

    tx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_DELAY_BYTES &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_tx == 2'd3
        |=> module_i2c.state_tx == ST_STOP
    );

    // -----------------------------------------------------------------------
    // TX FSM: STOP -> IDLE
    // -----------------------------------------------------------------------

    tx_stop_to_idle_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_STOP &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_tx == ST_IDLE
    );

    // -----------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en
    // -----------------------------------------------------------------------

    fifo_tx_rd_en_deasserted_in_idle: assert property (
        @(posedge PCLK) PRESETn && module_i2c.state_tx == ST_IDLE
        |=> fifo_tx_rd_en == 1'b0
    );

    fifo_tx_rd_en_asserted_after_data1_8_completes: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_RESP_DATA1 &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> fifo_tx_rd_en == 1'b1
    );

    fifo_tx_rd_en_deasserted_in_delay_bytes: assert property (
        @(posedge PCLK) PRESETn && module_i2c.state_tx == ST_DELAY_BYTES
        |=> fifo_tx_rd_en == 1'b0
    );

    fifo_tx_rd_en_deasserted_in_nack: assert property (
        @(posedge PCLK) PRESETn && module_i2c.state_tx == ST_NACK
        |=> fifo_tx_rd_en == 1'b0
    );

    // -----------------------------------------------------------------------
    // TX FSM: count_send_data resets each state transition
    // -----------------------------------------------------------------------

    count_send_data_reset_on_start_completion: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_START &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.count_send_data == 12'd0
    );

    count_send_data_reset_on_stop_completion: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_tx == ST_STOP &&
        module_i2c.count_send_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.count_send_data == 12'd0
    );

    // -----------------------------------------------------------------------
    // RX FSM: IDLE stay conditions
    // -----------------------------------------------------------------------

    rx_stays_idle_when_not_rx_mode: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_IDLE &&
        DATA_CONFIG_REG[0] == 1'b0 &&
        DATA_CONFIG_REG[1] == 1'b0
        |=> module_i2c.state_rx == ST_IDLE
    );

    rx_stays_idle_when_error_bits: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_IDLE &&
        DATA_CONFIG_REG[0] == 1'b1 &&
        DATA_CONFIG_REG[1] == 1'b1
        |=> module_i2c.state_rx == ST_IDLE
    );

    // -----------------------------------------------------------------------
    // RX FSM: STOP -> IDLE
    // -----------------------------------------------------------------------

    rx_stop_to_idle_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_STOP &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_IDLE
    );

    // -----------------------------------------------------------------------
    // RX FSM: CONTROLIN sequence
    // -----------------------------------------------------------------------

    rx_controlin_1_to_2_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_CONTROLIN_1 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_CONTROLIN_2
    );

    rx_controlin_8_to_response_cin_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_CONTROLIN_8 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_RESPONSE_CIN
    );

    // -----------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN -> ACK/NACK branch
    // -----------------------------------------------------------------------

    rx_response_cin_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESPONSE_CIN &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_rx == ST_DELAY_BYTES
    );

    rx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESPONSE_CIN &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_rx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // RX FSM: ADDRESS sequence
    // -----------------------------------------------------------------------

    rx_address_8_to_response_addr_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_ADDRESS_8 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_RESPONSE_ADDR
    );

    rx_response_addr_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESPONSE_ADDR &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_rx == ST_DELAY_BYTES
    );

    rx_response_addr_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESPONSE_ADDR &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_rx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // RX FSM: DATA0 sequence
    // -----------------------------------------------------------------------

    rx_data0_8_to_response_data0_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DATA0_8 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_RESP_DATA0
    );

    rx_response_data0_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESP_DATA0 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_rx == ST_DELAY_BYTES
    );

    rx_response_data0_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESP_DATA0 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_rx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // RX FSM: DATA1 sequence
    // -----------------------------------------------------------------------

    rx_data1_8_to_response_data1_on_count_match: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DATA1_8 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.state_rx == ST_RESP_DATA1
    );

    rx_response_data1_ack_to_delay: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESP_DATA1 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b0
        |=> module_i2c.state_rx == ST_DELAY_BYTES
    );

    rx_response_data1_nack_to_nack: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_RESP_DATA1 &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.RESPONSE == 1'b1
        |=> module_i2c.state_rx == ST_NACK
    );

    // -----------------------------------------------------------------------
    // RX FSM: DELAY_BYTES routing based on count_rx
    // -----------------------------------------------------------------------

    rx_delay_bytes_count0_to_address1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DELAY_BYTES &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_rx == 2'd0
        |=> module_i2c.state_rx == ST_ADDRESS_1
    );

    rx_delay_bytes_count1_to_data0_1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DELAY_BYTES &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_rx == 2'd1
        |=> module_i2c.state_rx == ST_DATA0_1
    );

    rx_delay_bytes_count2_to_data1_1: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DELAY_BYTES &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_rx == 2'd2
        |=> module_i2c.state_rx == ST_DATA1_1
    );

    rx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_DELAY_BYTES &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
        module_i2c.count_rx == 2'd3
        |=> module_i2c.state_rx == ST_STOP
    );

    // -----------------------------------------------------------------------
    // ENABLE_SDA / ENABLE_SCL
    // -----------------------------------------------------------------------

    enable_sda_high_in_rx_response_states: assert property (
        @(posedge PCLK) (module_i2c.state_rx == ST_RESPONSE_CIN ||
                         module_i2c.state_rx == ST_RESPONSE_ADDR ||
                         module_i2c.state_rx == ST_RESP_DATA0 ||
                         module_i2c.state_rx == ST_RESP_DATA1)
        |-> ENABLE_SDA == 1'b1
    );

    enable_sda_low_in_tx_response_states_not_rx: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == ST_RESPONSE_CIN ||
                          module_i2c.state_rx == ST_RESPONSE_ADDR ||
                          module_i2c.state_rx == ST_RESP_DATA0 ||
                          module_i2c.state_rx == ST_RESP_DATA1) &&
                         (module_i2c.state_tx == ST_RESPONSE_CIN ||
                          module_i2c.state_tx == ST_RESPONSE_ADDR ||
                          module_i2c.state_tx == ST_RESP_DATA0 ||
                          module_i2c.state_tx == ST_RESP_DATA1)
        |-> ENABLE_SDA == 1'b0
    );

    enable_scl_high_in_rx_response_states: assert property (
        @(posedge PCLK) (module_i2c.state_rx == ST_RESPONSE_CIN ||
                         module_i2c.state_rx == ST_RESPONSE_ADDR ||
                         module_i2c.state_rx == ST_RESP_DATA0 ||
                         module_i2c.state_rx == ST_RESP_DATA1)
        |-> ENABLE_SCL == 1'b1
    );

    enable_scl_high_in_tx_response_states_not_rx: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == ST_RESPONSE_CIN ||
                          module_i2c.state_rx == ST_RESPONSE_ADDR ||
                          module_i2c.state_rx == ST_RESP_DATA0 ||
                          module_i2c.state_rx == ST_RESP_DATA1) &&
                         (module_i2c.state_tx == ST_RESPONSE_CIN ||
                          module_i2c.state_tx == ST_RESPONSE_ADDR ||
                          module_i2c.state_tx == ST_RESP_DATA0 ||
                          module_i2c.state_tx == ST_RESP_DATA1)
        |-> ENABLE_SCL == 1'b1
    );

    enable_scl_low_otherwise: assert property (
        @(posedge PCLK) !(module_i2c.state_rx == ST_RESPONSE_CIN ||
                          module_i2c.state_rx == ST_RESPONSE_ADDR ||
                          module_i2c.state_rx == ST_RESP_DATA0 ||
                          module_i2c.state_rx == ST_RESP_DATA1) &&
                         !(module_i2c.state_tx == ST_RESPONSE_CIN ||
                           module_i2c.state_tx == ST_RESPONSE_ADDR ||
                           module_i2c.state_tx == ST_RESP_DATA0 ||
                           module_i2c.state_tx == ST_RESP_DATA1)
        |-> ENABLE_SCL == 1'b0
    );

    // -----------------------------------------------------------------------
    // count_timeout: resets when TX state is not IDLE
    // -----------------------------------------------------------------------

    count_timeout_resets_when_not_idle: assert property (
        @(posedge PCLK) PRESETn && module_i2c.state_tx != ST_IDLE
        |=> module_i2c.count_timeout == 12'd0
    );

    // -----------------------------------------------------------------------
    // count_tx / count_rx range
    // -----------------------------------------------------------------------

    count_tx_max_3: assert property (
        @(posedge PCLK) module_i2c.count_tx <= 2'd3
    );

    count_rx_max_3: assert property (
        @(posedge PCLK) module_i2c.count_rx <= 2'd3
    );

    // -----------------------------------------------------------------------
    // fifo_rx_wr_en deasserted in STOP and default
    // -----------------------------------------------------------------------

    fifo_rx_wr_en_deasserted_in_stop: assert property (
        @(posedge PCLK) PRESETn && module_i2c.state_rx == ST_STOP
        |=> fifo_rx_wr_en == 1'b0
    );

    // -----------------------------------------------------------------------
    // count_receive_data: resets on state completion
    // -----------------------------------------------------------------------

    count_receive_data_reset_on_start_completion: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_START &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.count_receive_data == 12'd0
    );

    count_receive_data_reset_on_stop_completion: assert property (
        @(posedge PCLK) PRESETn &&
        module_i2c.state_rx == ST_STOP &&
        module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]
        |=> module_i2c.count_receive_data == 12'd0
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
