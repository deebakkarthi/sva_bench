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

    // Local parameter definitions matching the DUT
    localparam [5:0] IDLE            = 6'd0;
    localparam [5:0] START           = 6'd1;
    localparam [5:0] CONTROLIN_1     = 6'd2;
    localparam [5:0] CONTROLIN_2     = 6'd3;
    localparam [5:0] CONTROLIN_3     = 6'd4;
    localparam [5:0] CONTROLIN_4     = 6'd5;
    localparam [5:0] CONTROLIN_5     = 6'd6;
    localparam [5:0] CONTROLIN_6     = 6'd7;
    localparam [5:0] CONTROLIN_7     = 6'd8;
    localparam [5:0] CONTROLIN_8     = 6'd9;
    localparam [5:0] RESPONSE_CIN    = 6'd10;
    localparam [5:0] ADDRESS_1       = 6'd11;
    localparam [5:0] ADDRESS_2       = 6'd12;
    localparam [5:0] ADDRESS_3       = 6'd13;
    localparam [5:0] ADDRESS_4       = 6'd14;
    localparam [5:0] ADDRESS_5       = 6'd15;
    localparam [5:0] ADDRESS_6       = 6'd16;
    localparam [5:0] ADDRESS_7       = 6'd17;
    localparam [5:0] ADDRESS_8       = 6'd18;
    localparam [5:0] RESPONSE_ADDRESS= 6'd19;
    localparam [5:0] DATA0_1         = 6'd20;
    localparam [5:0] DATA0_2         = 6'd21;
    localparam [5:0] DATA0_3         = 6'd22;
    localparam [5:0] DATA0_4         = 6'd23;
    localparam [5:0] DATA0_5         = 6'd24;
    localparam [5:0] DATA0_6         = 6'd25;
    localparam [5:0] DATA0_7         = 6'd26;
    localparam [5:0] DATA0_8         = 6'd27;
    localparam [5:0] RESPONSE_DATA0_1= 6'd28;
    localparam [5:0] DATA1_1         = 6'd29;
    localparam [5:0] DATA1_2         = 6'd30;
    localparam [5:0] DATA1_3         = 6'd31;
    localparam [5:0] DATA1_4         = 6'd32;
    localparam [5:0] DATA1_5         = 6'd33;
    localparam [5:0] DATA1_6         = 6'd34;
    localparam [5:0] DATA1_7         = 6'd35;
    localparam [5:0] DATA1_8         = 6'd36;
    localparam [5:0] RESPONSE_DATA1_1= 6'd37;
    localparam [5:0] DELAY_BYTES     = 6'd38;
    localparam [5:0] NACK            = 6'd39;
    localparam [5:0] STOP            = 6'd40;

    // -------------------------------------------------------------------------
    // TX_EMPTY reflects fifo_tx_f_empty
    // -------------------------------------------------------------------------
    tx_empty_reflects_fifo: assert property (
        @(posedge PCLK) TX_EMPTY == fifo_tx_f_empty
    );

    // -------------------------------------------------------------------------
    // RX_EMPTY reflects fifo_rx_f_empty
    // -------------------------------------------------------------------------
    rx_empty_reflects_fifo: assert property (
        @(posedge PCLK) RX_EMPTY == fifo_rx_f_empty
    );

    // -------------------------------------------------------------------------
    // ERROR is asserted only when DATA_CONFIG_REG[0]==1 and DATA_CONFIG_REG[1]==1
    // -------------------------------------------------------------------------
    error_when_both_config_bits_set: assert property (
        @(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
    );

    // -------------------------------------------------------------------------
    // On reset: state_tx goes to IDLE
    // -------------------------------------------------------------------------
    reset_state_tx_idle: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // On reset: state_rx goes to IDLE
    // -------------------------------------------------------------------------
    reset_state_rx_idle: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // On reset: count_send_data reset to 0
    // -------------------------------------------------------------------------
    reset_count_send_data_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_send_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // On reset: count_receive_data reset to 0
    // -------------------------------------------------------------------------
    reset_count_receive_data_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_receive_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // On reset: fifo_tx_rd_en deasserted
    // -------------------------------------------------------------------------
    reset_fifo_tx_rd_en_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // On reset: fifo_rx_wr_en deasserted
    // -------------------------------------------------------------------------
    reset_fifo_rx_wr_en_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (fifo_rx_wr_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // On reset: count_tx reset to 0
    // -------------------------------------------------------------------------
    reset_count_tx_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_tx == 2'd0)
    );

    // -------------------------------------------------------------------------
    // On reset: count_rx reset to 0
    // -------------------------------------------------------------------------
    reset_count_rx_zero: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.count_rx == 2'd0)
    );

    // -------------------------------------------------------------------------
    // On reset: BR_CLK_O reset to 1
    // -------------------------------------------------------------------------
    reset_br_clk_o_high: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    // -------------------------------------------------------------------------
    // On reset: BR_CLK_O_RX reset to 0
    // -------------------------------------------------------------------------
    reset_br_clk_o_rx_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.BR_CLK_O_RX == 1'b0)
    );

    // -------------------------------------------------------------------------
    // On reset: RESPONSE reset to 0
    // -------------------------------------------------------------------------
    reset_response_low: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.RESPONSE == 1'b0)
    );

    // -------------------------------------------------------------------------
    // count_timeout only increments in IDLE state when SDA==0 and SCL==0
    // -------------------------------------------------------------------------
    count_timeout_increments_only_in_idle: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // count_timeout resets when state_tx leaves IDLE
    // -------------------------------------------------------------------------
    count_timeout_reset_outside_idle: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        $fell(module_i2c.state_tx == IDLE) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: In IDLE, transitions to START only with correct configuration
    // -------------------------------------------------------------------------
    tx_idle_to_start_requires_config: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && $past(module_i2c.state_tx) == IDLE) |->
        (module_i2c.state_tx == START) ? (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) : 1'b1
    );

    // -------------------------------------------------------------------------
    // TX FSM: ERROR mode stays in IDLE
    // -------------------------------------------------------------------------
    tx_fsm_stays_idle_on_error: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |=>
        (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: Slave mode stays in IDLE
    // -------------------------------------------------------------------------
    tx_fsm_stays_idle_slave_mode: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |=>
        (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: STOP goes back to IDLE after counter expires
    // -------------------------------------------------------------------------
    tx_stop_returns_to_idle: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en asserted in RESPONSE_DATA1_1 when counter expires
    // -------------------------------------------------------------------------
    tx_rd_en_asserted_at_response_data1_end: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA1_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (fifo_tx_rd_en == 1'b1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en deasserted in IDLE
    // -------------------------------------------------------------------------
    tx_rd_en_deasserted_in_idle: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE) |->
        (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en deasserted in DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_rd_en_deasserted_in_delay_bytes: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES) |->
        (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: count_send_data resets to 0 when it reaches DATA_CONFIG_REG[13:2]
    // -------------------------------------------------------------------------
    tx_count_send_data_resets: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE && module_i2c.state_tx != NACK &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: CONTROLIN states advance sequentially
    // -------------------------------------------------------------------------
    tx_controlin1_to_2: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_2)
    );

    tx_controlin2_to_3: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_3)
    );

    tx_controlin3_to_4: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_3 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_4)
    );

    tx_controlin4_to_5: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_4 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_5)
    );

    tx_controlin5_to_6: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_5 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_6)
    );

    tx_controlin6_to_7: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_6 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_7)
    );

    tx_controlin7_to_8: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_8)
    );

    tx_controlin8_to_response: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_CIN)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_cin_ack_to_delay: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN NACK leads to NACK
    // -------------------------------------------------------------------------
    tx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == NACK)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_ADDRESS ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_address_ack_to_delay: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_ADDRESS && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA0_1 ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_data0_ack_to_delay: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA0_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA1_1 ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------
    tx_response_data1_ack_to_delay: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA1_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==3 leads to STOP
    // -------------------------------------------------------------------------
    tx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd3) |=>
        (module_i2c.state_tx == STOP)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==0 leads to ADDRESS_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count0_to_address1: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd0) |=>
        (module_i2c.state_tx == ADDRESS_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==1 leads to DATA0_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count1_to_data0: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd1) |=>
        (module_i2c.state_tx == DATA0_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==2 leads to DATA1_1
    // -------------------------------------------------------------------------
    tx_delay_bytes_count2_to_data1: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES && module_i2c.count_send_data == DATA_CONFIG_REG[13:2] && module_i2c.count_tx == 2'd2) |=>
        (module_i2c.state_tx == DATA1_1)
    );

    // -------------------------------------------------------------------------
    // ADDRESS states advance sequentially
    // -------------------------------------------------------------------------
    tx_address1_to_2: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_2)
    );

    tx_address8_to_response_address: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_ADDRESS)
    );

    // -------------------------------------------------------------------------
    // DATA0 states advance sequentially
    // -------------------------------------------------------------------------
    tx_data0_1_to_2: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA0_2)
    );

    tx_data0_8_to_response: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_DATA0_1)
    );

    // -------------------------------------------------------------------------
    // DATA1 states advance sequentially
    // -------------------------------------------------------------------------
    tx_data1_1_to_2: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA1_2)
    );

    tx_data1_8_to_response: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_DATA1_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: START goes to CONTROLIN_1
    // -------------------------------------------------------------------------
    tx_start_to_controlin1: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: On reset state_rx is IDLE
    // -------------------------------------------------------------------------
    rx_fsm_reset_idle: assert property (
        @(posedge PCLK) (!PRESETn) |=> (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: IDLE stays in IDLE when DATA_CONFIG_REG[0]==0 and DATA_CONFIG_REG[1]==0
    // -------------------------------------------------------------------------
    rx_idle_stays_idle_no_config: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |=>
        (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: IDLE stays in IDLE when DATA_CONFIG_REG[0]==1 and DATA_CONFIG_REG[1]==1
    // -------------------------------------------------------------------------
    rx_idle_stays_idle_error_config: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |=>
        (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: STOP goes to IDLE
    // -------------------------------------------------------------------------
    rx_stop_to_idle: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX FSM: fifo_rx_wr_en deasserted in STOP state
    // -------------------------------------------------------------------------
    rx_wr_en_deasserted_in_stop: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP) |->
        (fifo_rx_wr_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // RX FSM: CONTROLIN states advance sequentially
    // -------------------------------------------------------------------------
    rx_controlin1_to_2: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_1 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == CONTROLIN_2)
    );

    rx_controlin8_to_response_cin: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_CIN)
    );

    // -------------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------
    rx_response_cin_ack_to_delay: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_rx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN NACK leads to NACK
    // -------------------------------------------------------------------------
    rx_response_cin_nack_to_nack: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_rx == NACK)
    );

    // -------------------------------------------------------------------------
    // RX FSM: ADDRESS_8 goes to RESPONSE_ADDRESS
    // -------------------------------------------------------------------------
    rx_address8_to_response_address: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ADDRESS_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_ADDRESS)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES with count_rx==3 leads to STOP
    // -------------------------------------------------------------------------
    rx_delay_bytes_count3_to_stop: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd3) |=>
        (module_i2c.state_rx == STOP)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES with count_rx==0 leads to ADDRESS_1
    // -------------------------------------------------------------------------
    rx_delay_bytes_count0_to_address1: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd0) |=>
        (module_i2c.state_rx == ADDRESS_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DELAY_BYTES with count_rx==1 leads to DATA0_1
    // -------------------------------------------------------------------------
    rx_delay_bytes_count1_to_data0: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] && module_i2c.count_rx == 2'd1) |=>
        (module_i2c.state_rx == DATA0_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DATA0_8 goes to RESPONSE_DATA0_1
    // -------------------------------------------------------------------------
    rx_data0_8_to_response: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA0_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_DATA0_1)
    );

    // -------------------------------------------------------------------------
    // RX FSM: DATA1_8 goes to RESPONSE_DATA1_1
    // -------------------------------------------------------------------------
    rx_data1_8_to_response: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA1_8 && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_DATA1_1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA is 1 when state_rx is in RESPONSE states
    // -------------------------------------------------------------------------
    enable_sda_high_in_rx_response_states: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == RESPONSE_CIN ||
         module_i2c.state_rx == RESPONSE_ADDRESS ||
         module_i2c.state_rx == RESPONSE_DATA0_1 ||
         module_i2c.state_rx == RESPONSE_DATA1_1) |->
        (ENABLE_SDA == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL is 1 when state_rx is in RESPONSE states
    // -------------------------------------------------------------------------
    enable_scl_high_in_rx_response_states: assert property (
        @(posedge PCLK)
        (module_i2c.state_rx == RESPONSE_CIN ||
         module_i2c.state_rx == RESPONSE_ADDRESS ||
         module_i2c.state_rx == RESPONSE_DATA0_1 ||
         module_i2c.state_rx == RESPONSE_DATA1_1) |->
        (ENABLE_SCL == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL is 0 when state_tx is in RESPONSE states (not rx response)
    // -------------------------------------------------------------------------
    enable_scl_high_in_tx_response_states: assert property (
        @(posedge PCLK)
        (!(module_i2c.state_rx == RESPONSE_CIN ||
           module_i2c.state_rx == RESPONSE_ADDRESS ||
           module_i2c.state_rx == RESPONSE_DATA0_1 ||
           module_i2c.state_rx == RESPONSE_DATA1_1) &&
         (module_i2c.state_tx == RESPONSE_CIN ||
          module_i2c.state_tx == RESPONSE_ADDRESS ||
          module_i2c.state_tx == RESPONSE_DATA0_1 ||
          module_i2c.state_tx == RESPONSE_DATA1_1)) |->
        (ENABLE_SCL == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA is 0 when state_tx is in RESPONSE states (not rx response)
    // -------------------------------------------------------------------------
    enable_sda_low_in_tx_response_states: assert property (
        @(posedge PCLK)
        (!(module_i2c.state_rx == RESPONSE_CIN ||
           module_i2c.state_rx == RESPONSE_ADDRESS ||
           module_i2c.state_rx == RESPONSE_DATA0_1 ||
           module_i2c.state_rx == RESPONSE_DATA1_1) &&
         (module_i2c.state_tx == RESPONSE_CIN ||
          module_i2c.state_tx == RESPONSE_ADDRESS ||
          module_i2c.state_tx == RESPONSE_DATA0_1 ||
          module_i2c.state_tx == RESPONSE_DATA1_1)) |->
        (ENABLE_SDA == 1'b0)
    );

    // -------------------------------------------------------------------------
    // count_send_data never exceeds DATA_CONFIG_REG[13:2] in normal states
    // -------------------------------------------------------------------------
    count_send_data_bounded: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE && module_i2c.state_tx != NACK) |->
        (module_i2c.count_send_data <= DATA_CONFIG_REG[13:2])
    );

    // -------------------------------------------------------------------------
    // count_receive_data never exceeds DATA_CONFIG_REG[13:2] in normal RX states
    // -------------------------------------------------------------------------
    count_receive_data_bounded: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx != IDLE) |->
        (module_i2c.count_receive_data <= DATA_CONFIG_REG[13:2])
    );

    // -------------------------------------------------------------------------
    // count_tx stays within 2-bit range (0-3)
    // -------------------------------------------------------------------------
    count_tx_bounded: assert property (
        @(posedge PCLK) (module_i2c.count_tx <= 2'd3)
    );

    // -------------------------------------------------------------------------
    // count_rx stays within 2-bit range (0-3)
    // -------------------------------------------------------------------------
    count_rx_bounded: assert property (
        @(posedge PCLK) (module_i2c.count_rx <= 2'd3)
    );

    // -------------------------------------------------------------------------
    // TX FSM stays in START while count_send_data hasn't reached threshold
    // -------------------------------------------------------------------------
    tx_start_stays_until_count_reached: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START && module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == START)
    );

    // -------------------------------------------------------------------------
    // RX FSM: count_receive_data increments in non-IDLE states while below threshold
    // -------------------------------------------------------------------------
    rx_count_increments: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx != IDLE && module_i2c.state_rx != DELAY_BYTES &&
         module_i2c.count_receive_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == $past(module_i2c.count_receive_data) + 12'd1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: count_send_data increments in non-IDLE states while below threshold
    // -------------------------------------------------------------------------
    tx_count_increments: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE && module_i2c.state_tx != DELAY_BYTES &&
         module_i2c.state_tx != NACK &&
         module_i2c.count_send_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == $past(module_i2c.count_send_data) + 12'd1)
    );

    // -------------------------------------------------------------------------
    // count_timeout only increments when SDA and SCL are both low in IDLE
    // -------------------------------------------------------------------------
    count_timeout_increments_on_sda_scl_low: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && !(SDA == 1'b0 && SCL == 1'b0)) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: state_tx stays in IDLE when timeout has been reached
    // -------------------------------------------------------------------------
    tx_idle_stays_when_timeout_reached: assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE && module_i2c.count_timeout >= TIMEOUT_TX &&
         DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |=>
        (module_i2c.state_tx == IDLE)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
