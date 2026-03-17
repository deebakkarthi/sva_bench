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

    // localparam state values matching the DUT
    localparam [5:0] IDLE           = 6'd0,
                     START          = 6'd1,
                     CONTROLIN_1    = 6'd2,
                     CONTROLIN_2    = 6'd3,
                     CONTROLIN_3    = 6'd4,
                     CONTROLIN_4    = 6'd5,
                     CONTROLIN_5    = 6'd6,
                     CONTROLIN_6    = 6'd7,
                     CONTROLIN_7    = 6'd8,
                     CONTROLIN_8    = 6'd9,
                     RESPONSE_CIN   = 6'd10,
                     ADDRESS_1      = 6'd11,
                     ADDRESS_2      = 6'd12,
                     ADDRESS_3      = 6'd13,
                     ADDRESS_4      = 6'd14,
                     ADDRESS_5      = 6'd15,
                     ADDRESS_6      = 6'd16,
                     ADDRESS_7      = 6'd17,
                     ADDRESS_8      = 6'd18,
                     RESPONSE_ADDRESS = 6'd19,
                     DATA0_1        = 6'd20,
                     DATA0_2        = 6'd21,
                     DATA0_3        = 6'd22,
                     DATA0_4        = 6'd23,
                     DATA0_5        = 6'd24,
                     DATA0_6        = 6'd25,
                     DATA0_7        = 6'd26,
                     DATA0_8        = 6'd27,
                     RESPONSE_DATA0_1 = 6'd28,
                     DATA1_1        = 6'd29,
                     DATA1_2        = 6'd30,
                     DATA1_3        = 6'd31,
                     DATA1_4        = 6'd32,
                     DATA1_5        = 6'd33,
                     DATA1_6        = 6'd34,
                     DATA1_7        = 6'd35,
                     DATA1_8        = 6'd36,
                     RESPONSE_DATA1_1 = 6'd37,
                     DELAY_BYTES    = 6'd38,
                     NACK           = 6'd39,
                     STOP           = 6'd40;

    // -------------------------------------------------------------------------
    // TX_EMPTY reflects fifo_tx_f_empty
    // -------------------------------------------------------------------------
    tx_empty_reflects_fifo : assert property (
        @(posedge PCLK) (fifo_tx_f_empty == 1'b1) |-> (TX_EMPTY == 1'b1)
    );

    tx_empty_low_when_fifo_not_empty : assert property (
        @(posedge PCLK) (fifo_tx_f_empty == 1'b0) |-> (TX_EMPTY == 1'b0)
    );

    // -------------------------------------------------------------------------
    // RX_EMPTY reflects fifo_rx_f_empty
    // -------------------------------------------------------------------------
    rx_empty_reflects_fifo : assert property (
        @(posedge PCLK) (fifo_rx_f_empty == 1'b1) |-> (RX_EMPTY == 1'b1)
    );

    rx_empty_low_when_fifo_not_empty : assert property (
        @(posedge PCLK) (fifo_rx_f_empty == 1'b0) |-> (RX_EMPTY == 1'b0)
    );

    // -------------------------------------------------------------------------
    // ERROR is asserted only when both config bits are set
    // -------------------------------------------------------------------------
    error_when_both_config_bits_set : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1)
    );

    error_clear_when_config_bits_not_both_set : assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b0)
    );

    // -------------------------------------------------------------------------
    // After reset, TX state machine should be in IDLE
    // -------------------------------------------------------------------------
    reset_tx_state_idle : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // After reset, RX state machine should be in IDLE
    // -------------------------------------------------------------------------
    reset_rx_state_idle : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // After reset, fifo_tx_rd_en should be deasserted
    // -------------------------------------------------------------------------
    reset_fifo_tx_rd_en_low : assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // After reset, fifo_rx_wr_en should be deasserted
    // -------------------------------------------------------------------------
    reset_fifo_rx_wr_en_low : assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_rx_wr_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // After reset, count_send_data should be 0
    // -------------------------------------------------------------------------
    reset_count_send_data_zero : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_send_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // After reset, count_receive_data should be 0
    // -------------------------------------------------------------------------
    reset_count_receive_data_zero : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_receive_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // After reset, count_tx should be 0
    // -------------------------------------------------------------------------
    reset_count_tx_zero : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_tx == 2'd0)
    );

    // -------------------------------------------------------------------------
    // After reset, count_rx should be 0
    // -------------------------------------------------------------------------
    reset_count_rx_zero : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_rx == 2'd0)
    );

    // -------------------------------------------------------------------------
    // TX state machine should only be in valid states (0..40)
    // -------------------------------------------------------------------------
    tx_state_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx <= 6'd40)
    );

    // -------------------------------------------------------------------------
    // RX state machine should only be in valid states (0..40)
    // -------------------------------------------------------------------------
    rx_state_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx <= 6'd40)
    );

    // -------------------------------------------------------------------------
    // TX FSM: IDLE stays IDLE when enable bit not set and FIFO conditions hold
    // -------------------------------------------------------------------------
    tx_idle_stays_idle_when_disabled : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 &&
         (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
         DATA_CONFIG_REG[1] == 1'b0)
        |=> (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: IDLE stays IDLE when error condition present
    // -------------------------------------------------------------------------
    tx_idle_stays_idle_on_error : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b1 &&
         (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
         DATA_CONFIG_REG[1] == 1'b1)
        |=> (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: STOP eventually goes to IDLE when counter reaches threshold
    // -------------------------------------------------------------------------
    tx_stop_to_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: START moves to CONTROLIN_1 when count reaches threshold
    // -------------------------------------------------------------------------
    tx_start_to_controlin1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_1 stays if count not reached
    // -------------------------------------------------------------------------
    tx_controlin1_stays_when_counting : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_1 && module_i2c.count_send_data != DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_8 to RESPONSE_CIN when count reached
    // -------------------------------------------------------------------------
    tx_controlin8_to_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == RESPONSE_CIN)
    );

    // -------------------------------------------------------------------------
    // TX FSM: ADDRESS_8 to RESPONSE_ADDRESS when count reached
    // -------------------------------------------------------------------------
    tx_address8_to_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == RESPONSE_ADDRESS)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DATA0_8 to RESPONSE_DATA0_1 when count reached
    // -------------------------------------------------------------------------
    tx_data0_8_to_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == RESPONSE_DATA0_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DATA1_8 to RESPONSE_DATA1_1 when count reached
    // -------------------------------------------------------------------------
    tx_data1_8_to_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == RESPONSE_DATA1_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_cin_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN on NACK goes to NACK state
    // -------------------------------------------------------------------------
    tx_response_cin_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_tx == NACK)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_ADDRESS on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_address_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_ADDRESS &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA0_1 on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_data0_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA0_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA1_1 on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_data1_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==3 goes to STOP
    // -------------------------------------------------------------------------
    tx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd3)
        |=> (module_i2c.state_tx == STOP)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==0 goes to ADDRESS_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count0_to_address1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd0)
        |=> (module_i2c.state_tx == ADDRESS_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==1 goes to DATA0_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count1_to_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd1)
        |=> (module_i2c.state_tx == DATA0_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==2 goes to DATA1_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count2_to_data1_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd2)
        |=> (module_i2c.state_tx == DATA1_1)
    );

    // -------------------------------------------------------------------------
    // fifo_tx_rd_en deasserted in IDLE
    // -------------------------------------------------------------------------
    fifo_tx_rd_en_low_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE)
        |=> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // fifo_tx_rd_en deasserted in DELAY_BYTES
    // -------------------------------------------------------------------------
    fifo_tx_rd_en_low_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES)
        |=> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // fifo_tx_rd_en asserted after RESPONSE_DATA1_1 counter completes
    // -------------------------------------------------------------------------
    fifo_tx_rd_en_high_after_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (fifo_tx_rd_en == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA is high during RX response states
    // -------------------------------------------------------------------------
    enable_sda_high_in_rx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN ||
         module_i2c.state_rx == RESPONSE_ADDRESS ||
         module_i2c.state_rx == RESPONSE_DATA0_1 ||
         module_i2c.state_rx == RESPONSE_DATA1_1)
        |-> (ENABLE_SDA == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA is low during TX response states (when not in RX response)
    // -------------------------------------------------------------------------
    enable_sda_low_in_tx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!(module_i2c.state_rx == RESPONSE_CIN ||
           module_i2c.state_rx == RESPONSE_ADDRESS ||
           module_i2c.state_rx == RESPONSE_DATA0_1 ||
           module_i2c.state_rx == RESPONSE_DATA1_1) &&
         (module_i2c.state_tx == RESPONSE_CIN ||
          module_i2c.state_tx == RESPONSE_ADDRESS ||
          module_i2c.state_tx == RESPONSE_DATA0_1 ||
          module_i2c.state_tx == RESPONSE_DATA1_1))
        |-> (ENABLE_SDA == 1'b0)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL is high during TX response states (when not in RX response)
    // -------------------------------------------------------------------------
    enable_scl_high_in_tx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!(module_i2c.state_rx == RESPONSE_CIN ||
           module_i2c.state_rx == RESPONSE_ADDRESS ||
           module_i2c.state_rx == RESPONSE_DATA0_1 ||
           module_i2c.state_rx == RESPONSE_DATA1_1) &&
         (module_i2c.state_tx == RESPONSE_CIN ||
          module_i2c.state_tx == RESPONSE_ADDRESS ||
          module_i2c.state_tx == RESPONSE_DATA0_1 ||
          module_i2c.state_tx == RESPONSE_DATA1_1))
        |-> (ENABLE_SCL == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL is low when neither TX nor RX is in response state
    // -------------------------------------------------------------------------
    enable_scl_low_otherwise : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!(module_i2c.state_rx == RESPONSE_CIN ||
           module_i2c.state_rx == RESPONSE_ADDRESS ||
           module_i2c.state_rx == RESPONSE_DATA0_1 ||
           module_i2c.state_rx == RESPONSE_DATA1_1) &&
         !(module_i2c.state_tx == RESPONSE_CIN ||
           module_i2c.state_tx == RESPONSE_ADDRESS ||
           module_i2c.state_tx == RESPONSE_DATA0_1 ||
           module_i2c.state_tx == RESPONSE_DATA1_1))
        |-> (ENABLE_SCL == 1'b0)
    );

    // -------------------------------------------------------------------------
    // count_timeout resets to 0 when reset asserted
    // -------------------------------------------------------------------------
    reset_count_timeout_zero : assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // count_timeout only increments when in IDLE and SDA/SCL both low
    // -------------------------------------------------------------------------
    count_timeout_increments_only_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE)
        |=> (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_2 to CONTROLIN_3 when count reached
    // -------------------------------------------------------------------------
    tx_controlin2_to_controlin3 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_3)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_3 to CONTROLIN_4 when count reached
    // -------------------------------------------------------------------------
    tx_controlin3_to_controlin4 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_3 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_4)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_4 to CONTROLIN_5 when count reached
    // -------------------------------------------------------------------------
    tx_controlin4_to_controlin5 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_4 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_5)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_5 to CONTROLIN_6 when count reached
    // -------------------------------------------------------------------------
    tx_controlin5_to_controlin6 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_5 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_6)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_6 to CONTROLIN_7 when count reached
    // -------------------------------------------------------------------------
    tx_controlin6_to_controlin7 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_6 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_7)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN_7 to CONTROLIN_8 when count reached
    // -------------------------------------------------------------------------
    tx_controlin7_to_controlin8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == CONTROLIN_8)
    );

    // -------------------------------------------------------------------------
    // TX FSM: ADDRESS_1 to ADDRESS_2 when count reached
    // -------------------------------------------------------------------------
    tx_address1_to_address2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == ADDRESS_2)
    );

    // -------------------------------------------------------------------------
    // TX FSM: ADDRESS_7 to ADDRESS_8 when count reached
    // -------------------------------------------------------------------------
    tx_address7_to_address8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == ADDRESS_8)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DATA0_1 to DATA0_2 when count reached
    // -------------------------------------------------------------------------
    tx_data0_1_to_data0_2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == DATA0_2)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DATA1_1 to DATA1_2 when count reached
    // -------------------------------------------------------------------------
    tx_data1_1_to_data1_2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx == DATA1_2)
    );

    // -------------------------------------------------------------------------
    // RX FSM: STOP goes to IDLE when count reached
    // -------------------------------------------------------------------------
    rx_stop_to_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: CONTROLIN_8 to RESPONSE_CIN when count reached
    // -------------------------------------------------------------------------
    rx_controlin8_to_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx == RESPONSE_CIN)
    );

    // -------------------------------------------------------------------------
    // RX FSM: ADDRESS_8 to RESPONSE_ADDRESS when count reached
    // -------------------------------------------------------------------------
    rx_address8_to_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ADDRESS_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx == RESPONSE_ADDRESS)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DATA0_8 to RESPONSE_DATA0_1 when count reached
    // -------------------------------------------------------------------------
    rx_data0_8_to_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA0_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx == RESPONSE_DATA0_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DATA1_8 to RESPONSE_DATA1_1 when count reached
    // -------------------------------------------------------------------------
    rx_data1_8_to_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA1_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx == RESPONSE_DATA1_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM IDLE stays IDLE when config bits disable RX
    // -------------------------------------------------------------------------
    rx_idle_stays_idle_when_both_disabled : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0)
        |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM IDLE stays IDLE when error config
    // -------------------------------------------------------------------------
    rx_idle_stays_idle_when_error_config : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
        |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES count_rx==3 goes to STOP
    // -------------------------------------------------------------------------
    rx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd3)
        |=> (module_i2c.state_rx == STOP)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES count_rx==0 goes to ADDRESS_1
    // -------------------------------------------------------------------------
    rx_delay_bytes_count0_to_address1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd0)
        |=> (module_i2c.state_rx == ADDRESS_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES count_rx==1 goes to DATA0_1
    // -------------------------------------------------------------------------
    rx_delay_bytes_count1_to_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd1)
        |=> (module_i2c.state_rx == DATA0_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES count_rx==2 goes to DATA1_1
    // -------------------------------------------------------------------------
    rx_delay_bytes_count2_to_data1_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd2)
        |=> (module_i2c.state_rx == DATA1_1)
    );

    // -------------------------------------------------------------------------
    // count_tx is always within 0..3
    // -------------------------------------------------------------------------
    count_tx_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.count_tx <= 2'd3)
    );

    // -------------------------------------------------------------------------
    // count_rx is always within 0..3
    // -------------------------------------------------------------------------
    count_rx_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.count_rx <= 2'd3)
    );

    // -------------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------
    rx_response_cin_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_rx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN on NACK goes to NACK state
    // -------------------------------------------------------------------------
    rx_response_cin_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_rx == NACK)
    );

    // -------------------------------------------------------------------------
    // STOP state in RX: fifo_rx_wr_en deasserted
    // -------------------------------------------------------------------------
    rx_fifo_wr_en_low_in_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP)
        |=> (fifo_rx_wr_en == 1'b0)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
