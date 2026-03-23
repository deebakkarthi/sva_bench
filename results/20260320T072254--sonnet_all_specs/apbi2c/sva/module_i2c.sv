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

    // Local parameter values mirroring the DUT
    localparam IDLE            = 6'd0;
    localparam START           = 6'd1;
    localparam CONTROLIN_1     = 6'd2;
    localparam CONTROLIN_2     = 6'd3;
    localparam CONTROLIN_3     = 6'd4;
    localparam CONTROLIN_4     = 6'd5;
    localparam CONTROLIN_5     = 6'd6;
    localparam CONTROLIN_6     = 6'd7;
    localparam CONTROLIN_7     = 6'd8;
    localparam CONTROLIN_8     = 6'd9;
    localparam RESPONSE_CIN    = 6'd10;
    localparam ADDRESS_1       = 6'd11;
    localparam ADDRESS_2       = 6'd12;
    localparam ADDRESS_3       = 6'd13;
    localparam ADDRESS_4       = 6'd14;
    localparam ADDRESS_5       = 6'd15;
    localparam ADDRESS_6       = 6'd16;
    localparam ADDRESS_7       = 6'd17;
    localparam ADDRESS_8       = 6'd18;
    localparam RESPONSE_ADDRESS= 6'd19;
    localparam DATA0_1         = 6'd20;
    localparam DATA0_2         = 6'd21;
    localparam DATA0_3         = 6'd22;
    localparam DATA0_4         = 6'd23;
    localparam DATA0_5         = 6'd24;
    localparam DATA0_6         = 6'd25;
    localparam DATA0_7         = 6'd26;
    localparam DATA0_8         = 6'd27;
    localparam RESPONSE_DATA0_1= 6'd28;
    localparam DATA1_1         = 6'd29;
    localparam DATA1_2         = 6'd30;
    localparam DATA1_3         = 6'd31;
    localparam DATA1_4         = 6'd32;
    localparam DATA1_5         = 6'd33;
    localparam DATA1_6         = 6'd34;
    localparam DATA1_7         = 6'd35;
    localparam DATA1_8         = 6'd36;
    localparam RESPONSE_DATA1_1= 6'd37;
    localparam DELAY_BYTES     = 6'd38;
    localparam NACK            = 6'd39;
    localparam STOP            = 6'd40;

    // -------------------------------------------------------------------------
    // Output assignments
    // -------------------------------------------------------------------------

    tx_empty_reflects_fifo : assert property (
        @(posedge PCLK)
        TX_EMPTY == fifo_tx_f_empty
    );

    rx_empty_reflects_fifo : assert property (
        @(posedge PCLK)
        RX_EMPTY == fifo_rx_f_empty
    );

    error_when_both_config_bits_set : assert property (
        @(posedge PCLK)
        (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR
    );

    error_only_when_both_config_bits_set : assert property (
        @(posedge PCLK)
        ERROR |-> (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
    );

    // -------------------------------------------------------------------------
    // Reset behaviour - TX path
    // -------------------------------------------------------------------------

    reset_tx_state_idle : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.state_tx == IDLE)
    );

    reset_tx_count_send_data_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.count_send_data == 12'd0)
    );

    reset_fifo_tx_rd_en_low : assert property (
        @(posedge PCLK)
        !PRESETn |=> (fifo_tx_rd_en == 1'b0)
    );

    reset_tx_count_tx_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.count_tx == 2'd0)
    );

    reset_br_clk_o_high : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    reset_sda_out_high : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.SDA_OUT == 1'b1)
    );

    reset_response_low : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.RESPONSE == 1'b0)
    );

    // -------------------------------------------------------------------------
    // Reset behaviour - RX path
    // -------------------------------------------------------------------------

    reset_rx_state_idle : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.state_rx == IDLE)
    );

    reset_rx_count_receive_data_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.count_receive_data == 12'd0)
    );

    reset_fifo_rx_wr_en_low : assert property (
        @(posedge PCLK)
        !PRESETn |=> (fifo_rx_wr_en == 1'b0)
    );

    reset_rx_count_rx_zero : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.count_rx == 2'd0)
    );

    reset_br_clk_o_rx_low : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.BR_CLK_O_RX == 1'b0)
    );

    reset_sda_out_rx_low : assert property (
        @(posedge PCLK)
        !PRESETn |=> (module_i2c.SDA_OUT_RX == 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: state must be a legal value (0..40)
    // -------------------------------------------------------------------------

    tx_state_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_tx <= 6'd40
    );

    rx_state_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_rx <= 6'd40
    );

    // -------------------------------------------------------------------------
    // TX FSM: from IDLE, can only go to IDLE or START
    // -------------------------------------------------------------------------

    tx_idle_next_state_legal : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE) |=>
        (module_i2c.state_tx == IDLE || module_i2c.state_tx == START)
    );

    // -------------------------------------------------------------------------
    // TX FSM: STOP always goes back to IDLE
    // -------------------------------------------------------------------------

    tx_stop_eventually_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == IDLE)
    );

    // -------------------------------------------------------------------------
    // TX FSM: START transitions to CONTROLIN_1 when count reached
    // -------------------------------------------------------------------------

    tx_start_to_controlin1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: sequential state transitions when count reached
    // -------------------------------------------------------------------------

    tx_controlin1_to_controlin2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_2)
    );

    tx_controlin8_to_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_CIN)
    );

    tx_address8_to_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_ADDRESS)
    );

    tx_data0_8_to_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_DATA0_1)
    );

    tx_data1_8_to_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == RESPONSE_DATA1_1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN on ACK goes to DELAY_BYTES
    // -------------------------------------------------------------------------

    tx_response_cin_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    tx_response_cin_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == NACK)
    );

    tx_response_address_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_ADDRESS &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    tx_response_data0_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA0_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    tx_response_data1_ack_to_delay : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == DELAY_BYTES)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES with count_tx==3 goes to STOP
    // -------------------------------------------------------------------------

    tx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd3) |=>
        (module_i2c.state_tx == STOP)
    );

    // -------------------------------------------------------------------------
    // TX: fifo_tx_rd_en deasserted in IDLE
    // -------------------------------------------------------------------------

    tx_rd_en_low_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE) |=> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX: count_send_data increments by 1 each cycle when less than threshold
    // -------------------------------------------------------------------------

    tx_count_send_data_increments : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START &&
         module_i2c.count_send_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == $past(module_i2c.count_send_data) + 12'd1)
    );

    // -------------------------------------------------------------------------
    // TX: count_send_data resets to 0 when threshold reached (non-IDLE states)
    // -------------------------------------------------------------------------

    tx_count_resets_at_threshold_controlin1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX: count_tx does not exceed 3
    // -------------------------------------------------------------------------

    tx_count_tx_max_3 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_tx <= 2'd3
    );

    // -------------------------------------------------------------------------
    // RX FSM: from IDLE, can only go to IDLE or START
    // -------------------------------------------------------------------------

    rx_idle_next_state_legal : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE) |=>
        (module_i2c.state_rx == IDLE || module_i2c.state_rx == START)
    );

    // -------------------------------------------------------------------------
    // RX FSM: STOP goes back to IDLE when count reached
    // -------------------------------------------------------------------------

    rx_stop_to_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == IDLE)
    );

    // -------------------------------------------------------------------------
    // RX: fifo_rx_wr_en deasserted in STOP
    // -------------------------------------------------------------------------

    rx_wr_en_low_in_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == STOP) |=> (fifo_rx_wr_en == 1'b0)
    );

    // -------------------------------------------------------------------------
    // RX: count_receive_data increments in data states
    // -------------------------------------------------------------------------

    rx_count_receive_data_increments_in_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA0_1 &&
         module_i2c.count_receive_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == $past(module_i2c.count_receive_data) + 12'd1)
    );

    // -------------------------------------------------------------------------
    // RX: count_rx does not exceed 3
    // -------------------------------------------------------------------------

    rx_count_rx_max_3 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_rx <= 2'd3
    );

    // -------------------------------------------------------------------------
    // ERROR: when both config bits 0 and 1 are set
    // -------------------------------------------------------------------------

    error_high_implies_no_tx_mode : assert property (
        @(posedge PCLK)
        ERROR |-> (DATA_CONFIG_REG[1] == 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA: reflects response states correctly
    // -------------------------------------------------------------------------

    enable_sda_high_during_rx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == RESPONSE_CIN    ||
         module_i2c.state_rx == RESPONSE_ADDRESS ||
         module_i2c.state_rx == RESPONSE_DATA0_1 ||
         module_i2c.state_rx == RESPONSE_DATA1_1) |->
        ENABLE_SDA
    );

    enable_sda_low_during_tx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx != RESPONSE_CIN     &&
         module_i2c.state_rx != RESPONSE_ADDRESS  &&
         module_i2c.state_rx != RESPONSE_DATA0_1  &&
         module_i2c.state_rx != RESPONSE_DATA1_1  &&
         (module_i2c.state_tx == RESPONSE_CIN     ||
          module_i2c.state_tx == RESPONSE_ADDRESS  ||
          module_i2c.state_tx == RESPONSE_DATA0_1  ||
          module_i2c.state_tx == RESPONSE_DATA1_1)) |->
        !ENABLE_SDA
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL: high during TX response states
    // -------------------------------------------------------------------------

    enable_scl_high_during_tx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx != RESPONSE_CIN     &&
         module_i2c.state_rx != RESPONSE_ADDRESS  &&
         module_i2c.state_rx != RESPONSE_DATA0_1  &&
         module_i2c.state_rx != RESPONSE_DATA1_1  &&
         (module_i2c.state_tx == RESPONSE_CIN     ||
          module_i2c.state_tx == RESPONSE_ADDRESS  ||
          module_i2c.state_tx == RESPONSE_DATA0_1  ||
          module_i2c.state_tx == RESPONSE_DATA1_1)) |->
        ENABLE_SCL
    );

    // -------------------------------------------------------------------------
    // Timeout counter: resets when state_tx leaves IDLE
    // -------------------------------------------------------------------------

    timeout_resets_when_not_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != IDLE) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    // -------------------------------------------------------------------------
    // Timeout counter: only increments when SDA and SCL are both 0 in IDLE
    // -------------------------------------------------------------------------

    timeout_increments_only_on_sda_scl_low : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE &&
         module_i2c.count_timeout <= TIMEOUT_TX &&
         !(SDA == 1'b0 && SCL == 1'b0)) |=>
        (module_i2c.count_timeout == $past(module_i2c.count_timeout))
    );

    // -------------------------------------------------------------------------
    // TX mode requires DATA_CONFIG_REG[0]==1 and DATA_CONFIG_REG[1]==0
    // -------------------------------------------------------------------------

    tx_start_requires_tx_mode : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == IDLE) &&
        (module_i2c.next_state_tx == START) |->
        (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0)
    );

    // -------------------------------------------------------------------------
    // RX mode: rx START only when DATA_CONFIG_REG[1]==1 and DATA_CONFIG_REG[0]==0
    // -------------------------------------------------------------------------

    rx_start_requires_rx_mode : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == IDLE) &&
        (module_i2c.next_state_rx == START) |->
        (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1)
    );

    // -------------------------------------------------------------------------
    // TX: CONTROLIN sequence is always 1->2->3->4->5->6->7->8
    // -------------------------------------------------------------------------

    tx_controlin2_to_controlin3 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_3)
    );

    tx_controlin3_to_controlin4 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_3 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_4)
    );

    tx_controlin4_to_controlin5 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_4 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_5)
    );

    tx_controlin5_to_controlin6 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_5 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_6)
    );

    tx_controlin6_to_controlin7 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_6 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_7)
    );

    tx_controlin7_to_controlin8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_8)
    );

    // -------------------------------------------------------------------------
    // TX ADDRESS sequence
    // -------------------------------------------------------------------------

    tx_address1_to_address2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_2)
    );

    tx_address2_to_address3 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_2 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_3)
    );

    tx_address3_to_address4 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_3 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_4)
    );

    tx_address4_to_address5 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_4 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_5)
    );

    tx_address5_to_address6 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_5 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_6)
    );

    tx_address6_to_address7 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_6 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_7)
    );

    tx_address7_to_address8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ADDRESS_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ADDRESS_8)
    );

    // -------------------------------------------------------------------------
    // TX DATA0 sequence
    // -------------------------------------------------------------------------

    tx_data0_1_to_data0_2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA0_2)
    );

    tx_data0_7_to_data0_8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA0_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA0_8)
    );

    // -------------------------------------------------------------------------
    // TX DATA1 sequence
    // -------------------------------------------------------------------------

    tx_data1_1_to_data1_2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA1_2)
    );

    tx_data1_7_to_data1_8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DATA1_7 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == DATA1_8)
    );

    // -------------------------------------------------------------------------
    // TX: state stays in same state when count not reached
    // -------------------------------------------------------------------------

    tx_state_stable_when_count_not_reached_start : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == START &&
         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == START)
    );

    tx_state_stable_when_count_not_reached_controlin1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == CONTROLIN_1 &&
         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == CONTROLIN_1)
    );

    tx_state_stable_when_count_not_reached_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == STOP &&
         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == STOP)
    );

    // -------------------------------------------------------------------------
    // RX: count_receive_data resets when threshold reached
    // -------------------------------------------------------------------------

    rx_count_resets_at_threshold_controlin1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == 12'd0)
    );

    rx_count_resets_at_threshold_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA0_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == 12'd0)
    );

    // -------------------------------------------------------------------------
    // RX FSM sequential transitions
    // -------------------------------------------------------------------------

    rx_controlin1_to_controlin2 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == CONTROLIN_2)
    );

    rx_controlin8_to_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == CONTROLIN_8 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_CIN)
    );

    rx_address8_to_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ADDRESS_8 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_ADDRESS)
    );

    rx_data0_8_to_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA0_8 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_DATA0_1)
    );

    rx_data1_8_to_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DATA1_8 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == RESPONSE_DATA1_1)
    );

    rx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd3) |=>
        (module_i2c.state_rx == STOP)
    );

    // -------------------------------------------------------------------------
    // TX: DELAY_BYTES with count_tx==0 goes to ADDRESS_1
    // -------------------------------------------------------------------------

    tx_delay_bytes_count0_to_address1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd0) |=>
        (module_i2c.state_tx == ADDRESS_1)
    );

    tx_delay_bytes_count1_to_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd1) |=>
        (module_i2c.state_tx == DATA0_1)
    );

    tx_delay_bytes_count2_to_data1_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd2) |=>
        (module_i2c.state_tx == DATA1_1)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
