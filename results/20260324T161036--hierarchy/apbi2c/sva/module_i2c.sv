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

    localparam [5:0] ST_IDLE             = 6'd0,
                     ST_START            = 6'd1,
                     ST_CONTROLIN_1      = 6'd2,
                     ST_CONTROLIN_2      = 6'd3,
                     ST_CONTROLIN_3      = 6'd4,
                     ST_CONTROLIN_4      = 6'd5,
                     ST_CONTROLIN_5      = 6'd6,
                     ST_CONTROLIN_6      = 6'd7,
                     ST_CONTROLIN_7      = 6'd8,
                     ST_CONTROLIN_8      = 6'd9,
                     ST_RESPONSE_CIN     = 6'd10,
                     ST_ADDRESS_1        = 6'd11,
                     ST_ADDRESS_2        = 6'd12,
                     ST_ADDRESS_3        = 6'd13,
                     ST_ADDRESS_4        = 6'd14,
                     ST_ADDRESS_5        = 6'd15,
                     ST_ADDRESS_6        = 6'd16,
                     ST_ADDRESS_7        = 6'd17,
                     ST_ADDRESS_8        = 6'd18,
                     ST_RESPONSE_ADDRESS = 6'd19,
                     ST_DATA0_1          = 6'd20,
                     ST_DATA0_2          = 6'd21,
                     ST_DATA0_3          = 6'd22,
                     ST_DATA0_4          = 6'd23,
                     ST_DATA0_5          = 6'd24,
                     ST_DATA0_6          = 6'd25,
                     ST_DATA0_7          = 6'd26,
                     ST_DATA0_8          = 6'd27,
                     ST_RESPONSE_DATA0_1 = 6'd28,
                     ST_DATA1_1          = 6'd29,
                     ST_DATA1_2          = 6'd30,
                     ST_DATA1_3          = 6'd31,
                     ST_DATA1_4          = 6'd32,
                     ST_DATA1_5          = 6'd33,
                     ST_DATA1_6          = 6'd34,
                     ST_DATA1_7          = 6'd35,
                     ST_DATA1_8          = 6'd36,
                     ST_RESPONSE_DATA1_1 = 6'd37,
                     ST_DELAY_BYTES      = 6'd38,
                     ST_NACK             = 6'd39,
                     ST_STOP             = 6'd40;

    // ------------------------------------------------------------------
    // Combinational output correctness
    // ------------------------------------------------------------------

    tx_empty_equals_fifo_tx_f_empty : assert property (
        @(posedge PCLK) TX_EMPTY == fifo_tx_f_empty
    );

    rx_empty_equals_fifo_rx_f_empty : assert property (
        @(posedge PCLK) RX_EMPTY == fifo_rx_f_empty
    );

    error_when_both_config_bits_set : assert property (
        @(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] & DATA_CONFIG_REG[1])
    );

    // ------------------------------------------------------------------
    // Reset behaviour - TX path
    // ------------------------------------------------------------------

    tx_state_resets_to_idle : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == ST_IDLE)
    );

    count_send_data_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0)
    );

    fifo_tx_rd_en_deasserted_after_reset : assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_tx_rd_en
    );

    count_tx_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_tx == 2'd0)
    );

    br_clk_o_resets_to_one : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1)
    );

    sda_out_resets_to_one : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.SDA_OUT == 1'b1)
    );

    response_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.RESPONSE == 1'b0)
    );

    // ------------------------------------------------------------------
    // Reset behaviour - RX path
    // ------------------------------------------------------------------

    rx_state_resets_to_idle : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == ST_IDLE)
    );

    count_receive_data_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0)
    );

    fifo_rx_wr_en_deasserted_after_reset : assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_rx_wr_en
    );

    count_rx_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_rx == 2'd0)
    );

    br_clk_o_rx_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O_RX == 1'b0)
    );

    sda_out_rx_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.SDA_OUT_RX == 1'b0)
    );

    // ------------------------------------------------------------------
    // Reset behaviour - timeout counter
    // ------------------------------------------------------------------

    count_timeout_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_timeout == 12'd0)
    );

    // ------------------------------------------------------------------
    // State machine valid ranges
    // ------------------------------------------------------------------

    tx_state_in_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_tx <= 6'd40
    );

    rx_state_in_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_rx <= 6'd40
    );

    // ------------------------------------------------------------------
    // Counter bounds
    // ------------------------------------------------------------------

    count_tx_bounded : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_tx <= 2'd3
    );

    count_rx_bounded : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_rx <= 2'd3
    );

    // ------------------------------------------------------------------
    // State machine sequential update (state <- next_state each cycle)
    // ------------------------------------------------------------------

    tx_state_updates_from_next_state : assert property (
        @(posedge PCLK)
        $past(PRESETn) |-> (module_i2c.state_tx == $past(module_i2c.next_state_tx))
    );

    rx_state_updates_from_next_state : assert property (
        @(posedge PCLK)
        $past(PRESETn) |-> (module_i2c.state_rx == $past(module_i2c.next_state_rx))
    );

    // ------------------------------------------------------------------
    // ENABLE_SDA assignments
    // ------------------------------------------------------------------

    enable_sda_high_during_rx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_CIN     ||
         module_i2c.state_rx == ST_RESPONSE_ADDRESS ||
         module_i2c.state_rx == ST_RESPONSE_DATA0_1 ||
         module_i2c.state_rx == ST_RESPONSE_DATA1_1) |-> (ENABLE_SDA == 1'b1)
    );

    enable_sda_low_during_tx_response_states_only : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        ((module_i2c.state_tx == ST_RESPONSE_CIN     ||
          module_i2c.state_tx == ST_RESPONSE_ADDRESS ||
          module_i2c.state_tx == ST_RESPONSE_DATA0_1 ||
          module_i2c.state_tx == ST_RESPONSE_DATA1_1) &&
         !(module_i2c.state_rx == ST_RESPONSE_CIN     ||
           module_i2c.state_rx == ST_RESPONSE_ADDRESS ||
           module_i2c.state_rx == ST_RESPONSE_DATA0_1 ||
           module_i2c.state_rx == ST_RESPONSE_DATA1_1)) |-> (ENABLE_SDA == 1'b0)
    );

    enable_sda_high_when_neither_state_in_response : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!(module_i2c.state_rx == ST_RESPONSE_CIN     ||
           module_i2c.state_rx == ST_RESPONSE_ADDRESS ||
           module_i2c.state_rx == ST_RESPONSE_DATA0_1 ||
           module_i2c.state_rx == ST_RESPONSE_DATA1_1) &&
         !(module_i2c.state_tx == ST_RESPONSE_CIN     ||
           module_i2c.state_tx == ST_RESPONSE_ADDRESS ||
           module_i2c.state_tx == ST_RESPONSE_DATA0_1 ||
           module_i2c.state_tx == ST_RESPONSE_DATA1_1)) |-> (ENABLE_SDA == 1'b1)
    );

    // ------------------------------------------------------------------
    // ENABLE_SCL assignments
    // ------------------------------------------------------------------

    enable_scl_high_during_rx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_CIN     ||
         module_i2c.state_rx == ST_RESPONSE_ADDRESS ||
         module_i2c.state_rx == ST_RESPONSE_DATA0_1 ||
         module_i2c.state_rx == ST_RESPONSE_DATA1_1) |-> (ENABLE_SCL == 1'b1)
    );

    enable_scl_high_during_tx_response_states : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_CIN     ||
         module_i2c.state_tx == ST_RESPONSE_ADDRESS ||
         module_i2c.state_tx == ST_RESPONSE_DATA0_1 ||
         module_i2c.state_tx == ST_RESPONSE_DATA1_1) |-> (ENABLE_SCL == 1'b1)
    );

    enable_scl_low_when_no_response_state_active : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!(module_i2c.state_rx == ST_RESPONSE_CIN     ||
           module_i2c.state_rx == ST_RESPONSE_ADDRESS ||
           module_i2c.state_rx == ST_RESPONSE_DATA0_1 ||
           module_i2c.state_rx == ST_RESPONSE_DATA1_1) &&
         !(module_i2c.state_tx == ST_RESPONSE_CIN     ||
           module_i2c.state_tx == ST_RESPONSE_ADDRESS ||
           module_i2c.state_tx == ST_RESPONSE_DATA0_1 ||
           module_i2c.state_tx == ST_RESPONSE_DATA1_1)) |-> (ENABLE_SCL == 1'b0)
    );

    // ------------------------------------------------------------------
    // TX FSM: IDLE transitions
    // ------------------------------------------------------------------

    tx_idle_stays_idle_when_config0_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b0 &&
         (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
         DATA_CONFIG_REG[1] == 1'b0) |=>
        (module_i2c.state_tx == ST_IDLE)
    );

    tx_idle_stays_idle_when_error_condition : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b1 &&
         (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) &&
         DATA_CONFIG_REG[1] == 1'b1) |=>
        (module_i2c.state_tx == ST_IDLE)
    );

    tx_idle_to_start_when_enabled : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b1 &&
         ((fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b0) || fifo_tx_f_full == 1'b1) &&
         DATA_CONFIG_REG[1] == 1'b0 &&
         module_i2c.count_timeout < TIMEOUT_TX) |=>
        (module_i2c.state_tx == ST_START)
    );

    // ------------------------------------------------------------------
    // TX FSM: STOP transitions
    // ------------------------------------------------------------------

    tx_stop_to_idle_when_count_matches : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_STOP &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ST_IDLE)
    );

    tx_stop_stays_in_stop_when_count_not_reached : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_STOP &&
         module_i2c.count_send_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_tx == ST_STOP)
    );

    // ------------------------------------------------------------------
    // TX FSM: RESPONSE_CIN transitions
    // ------------------------------------------------------------------

    tx_response_cin_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == ST_DELAY_BYTES)
    );

    tx_response_cin_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_CIN &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // TX FSM: RESPONSE_ADDRESS transitions
    // ------------------------------------------------------------------

    tx_response_address_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_ADDRESS &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == ST_DELAY_BYTES)
    );

    tx_response_address_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_ADDRESS &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA0_1 transitions
    // ------------------------------------------------------------------

    tx_response_data0_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_DATA0_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == ST_DELAY_BYTES)
    );

    tx_response_data0_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_DATA0_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // TX FSM: RESPONSE_DATA1_1 transitions
    // ------------------------------------------------------------------

    tx_response_data1_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_tx == ST_DELAY_BYTES)
    );

    tx_response_data1_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_tx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // TX FSM: DELAY_BYTES transitions (based on count_tx)
    // ------------------------------------------------------------------

    tx_delay_bytes_to_address1_when_count_tx_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd0) |=>
        (module_i2c.state_tx == ST_ADDRESS_1)
    );

    tx_delay_bytes_to_data0_when_count_tx_one : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd1) |=>
        (module_i2c.state_tx == ST_DATA0_1)
    );

    tx_delay_bytes_to_data1_when_count_tx_two : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd2) |=>
        (module_i2c.state_tx == ST_DATA1_1)
    );

    tx_delay_bytes_to_stop_when_count_tx_three : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd3) |=>
        (module_i2c.state_tx == ST_STOP)
    );

    // ------------------------------------------------------------------
    // TX FSM: count_tx increments in DELAY_BYTES
    // ------------------------------------------------------------------

    tx_count_tx_increments_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx < 2'd3) |=>
        (module_i2c.count_tx == ($past(module_i2c.count_tx) + 2'd1))
    );

    tx_count_tx_wraps_to_zero_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd3) |=>
        (module_i2c.count_tx == 2'd0)
    );

    // ------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en cleared in IDLE, DELAY_BYTES, NACK
    // ------------------------------------------------------------------

    fifo_tx_rd_en_cleared_after_idle_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_IDLE) |=> !fifo_tx_rd_en
    );

    fifo_tx_rd_en_cleared_after_delay_bytes_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_DELAY_BYTES) |=> !fifo_tx_rd_en
    );

    fifo_tx_rd_en_cleared_after_nack_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_NACK) |=> !fifo_tx_rd_en
    );

    // ------------------------------------------------------------------
    // TX FSM: count_send_data increments while less than target
    // ------------------------------------------------------------------

    tx_count_send_data_increments_in_start : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_START &&
         module_i2c.count_send_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == ($past(module_i2c.count_send_data) + 12'd1))
    );

    tx_count_send_data_resets_in_start : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_START &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_send_data == 12'd0)
    );

    // ------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en asserted after RESPONSE_DATA1_1 count done
    // ------------------------------------------------------------------

    fifo_tx_rd_en_asserted_after_response_data1_count_done : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_RESPONSE_DATA1_1 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
        fifo_tx_rd_en
    );

    // ------------------------------------------------------------------
    // TX FSM: count_timeout behaviour
    // ------------------------------------------------------------------

    count_timeout_clears_when_tx_not_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx != ST_IDLE) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    count_timeout_clears_when_exceeds_timeout_tx : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.count_timeout > TIMEOUT_TX) |=>
        (module_i2c.count_timeout == 12'd0)
    );

    count_timeout_increments_when_sda_scl_low_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx == ST_IDLE &&
         module_i2c.count_timeout <= TIMEOUT_TX &&
         SDA == 1'b0 && SCL == 1'b0) |=>
        (module_i2c.count_timeout == ($past(module_i2c.count_timeout) + 12'd1))
    );

    // ------------------------------------------------------------------
    // RX FSM: IDLE transitions
    // ------------------------------------------------------------------

    rx_idle_stays_idle_when_both_config_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b0 &&
         DATA_CONFIG_REG[1] == 1'b0) |=>
        (module_i2c.state_rx == ST_IDLE)
    );

    rx_idle_stays_idle_when_both_config_one : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b1 &&
         DATA_CONFIG_REG[1] == 1'b1) |=>
        (module_i2c.state_rx == ST_IDLE)
    );

    rx_idle_to_start_when_rx_mode_and_sda_scl_low : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_IDLE &&
         DATA_CONFIG_REG[0] == 1'b0 &&
         DATA_CONFIG_REG[1] == 1'b1 &&
         module_i2c.SDA_OUT_RX == 1'b0 &&
         module_i2c.BR_CLK_O_RX == 1'b0) |=>
        (module_i2c.state_rx == ST_START)
    );

    // ------------------------------------------------------------------
    // RX FSM: STOP transitions
    // ------------------------------------------------------------------

    rx_stop_to_idle_when_count_matches : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_STOP &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == ST_IDLE)
    );

    rx_stop_stays_in_stop_when_count_not_reached : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_STOP &&
         module_i2c.count_receive_data != DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.state_rx == ST_STOP)
    );

    // ------------------------------------------------------------------
    // RX FSM: DELAY_BYTES transitions (based on count_rx)
    // ------------------------------------------------------------------

    rx_delay_bytes_to_address1_when_count_rx_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd0) |=>
        (module_i2c.state_rx == ST_ADDRESS_1)
    );

    rx_delay_bytes_to_data0_when_count_rx_one : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd1) |=>
        (module_i2c.state_rx == ST_DATA0_1)
    );

    rx_delay_bytes_to_data1_when_count_rx_two : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd2) |=>
        (module_i2c.state_rx == ST_DATA1_1)
    );

    rx_delay_bytes_to_stop_when_count_rx_three : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd3) |=>
        (module_i2c.state_rx == ST_STOP)
    );

    // ------------------------------------------------------------------
    // RX FSM: RESPONSE_CIN transitions
    // ------------------------------------------------------------------

    rx_response_cin_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_CIN &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_rx == ST_DELAY_BYTES)
    );

    rx_response_cin_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_CIN &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_rx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // RX FSM: RESPONSE_ADDRESS transitions
    // ------------------------------------------------------------------

    rx_response_address_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_ADDRESS &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_rx == ST_DELAY_BYTES)
    );

    rx_response_address_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_ADDRESS &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_rx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // RX FSM: RESPONSE_DATA0_1 transitions
    // ------------------------------------------------------------------

    rx_response_data0_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_DATA0_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_rx == ST_DELAY_BYTES)
    );

    rx_response_data0_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_DATA0_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_rx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // RX FSM: RESPONSE_DATA1_1 transitions
    // ------------------------------------------------------------------

    rx_response_data1_ack_goes_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_DATA1_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0) |=>
        (module_i2c.state_rx == ST_DELAY_BYTES)
    );

    rx_response_data1_nack_goes_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_RESPONSE_DATA1_1 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1) |=>
        (module_i2c.state_rx == ST_NACK)
    );

    // ------------------------------------------------------------------
    // RX FSM: fifo_rx_wr_en cleared in STOP and default
    // ------------------------------------------------------------------

    fifo_rx_wr_en_cleared_after_stop_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_STOP) |=> !fifo_rx_wr_en
    );

    // ------------------------------------------------------------------
    // RX FSM: count_receive_data increments while less than target
    // ------------------------------------------------------------------

    rx_count_receive_data_increments_in_start : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_START &&
         module_i2c.count_receive_data < DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == ($past(module_i2c.count_receive_data) + 12'd1))
    );

    rx_count_receive_data_resets_in_start : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_START &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
        (module_i2c.count_receive_data == 12'd0)
    );

    // ------------------------------------------------------------------
    // RX FSM: count_rx increments in DELAY_BYTES
    // ------------------------------------------------------------------

    rx_count_rx_increments_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd0) |=>
        (module_i2c.count_rx == 2'd1)
    );

    rx_count_rx_wraps_to_zero_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx == ST_DELAY_BYTES &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd3) |=>
        (module_i2c.count_rx == 2'd0)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
