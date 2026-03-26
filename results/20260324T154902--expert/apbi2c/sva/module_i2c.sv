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

    // -------------------------------------------------------------------------
    // Combinational output correctness
    // -------------------------------------------------------------------------

    tx_empty_mirrors_fifo_tx_f_empty : assert property (
        @(posedge PCLK) TX_EMPTY === fifo_tx_f_empty
    );

    rx_empty_mirrors_fifo_rx_f_empty : assert property (
        @(posedge PCLK) RX_EMPTY === fifo_rx_f_empty
    );

    error_active_only_when_both_config_bits_set : assert property (
        @(posedge PCLK) ERROR === (DATA_CONFIG_REG[0] & DATA_CONFIG_REG[1])
    );

    error_deasserted_when_config_bit0_low : assert property (
        @(posedge PCLK) (!DATA_CONFIG_REG[0]) |-> !ERROR
    );

    error_deasserted_when_config_bit1_low : assert property (
        @(posedge PCLK) (!DATA_CONFIG_REG[1]) |-> !ERROR
    );

    // -------------------------------------------------------------------------
    // Reset behavior - TX path
    // -------------------------------------------------------------------------

    reset_state_tx_to_idle : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_tx === 6'd0)
    );

    reset_count_send_data_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data === 12'd0)
    );

    reset_sda_out_high : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.SDA_OUT === 1'b1)
    );

    reset_fifo_tx_rd_en_low : assert property (
        @(posedge PCLK) !PRESETn |=> (fifo_tx_rd_en === 1'b0)
    );

    reset_count_tx_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_tx === 2'd0)
    );

    reset_br_clk_o_high : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O === 1'b1)
    );

    reset_response_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.RESPONSE === 1'b0)
    );

    // -------------------------------------------------------------------------
    // Reset behavior - RX path
    // -------------------------------------------------------------------------

    reset_state_rx_to_idle : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.state_rx === 6'd0)
    );

    reset_count_receive_data_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data === 12'd0)
    );

    reset_sda_out_rx_low : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.SDA_OUT_RX === 1'b0)
    );

    reset_fifo_rx_wr_en_low : assert property (
        @(posedge PCLK) !PRESETn |=> (fifo_rx_wr_en === 1'b0)
    );

    reset_count_rx_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_rx === 2'd0)
    );

    reset_br_clk_o_rx_low : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O_RX === 1'b0)
    );

    // -------------------------------------------------------------------------
    // Reset behavior - timeout counter
    // -------------------------------------------------------------------------

    reset_count_timeout_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (module_i2c.count_timeout === 12'd0)
    );

    // -------------------------------------------------------------------------
    // State validity
    // -------------------------------------------------------------------------

    state_tx_within_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_tx <= 6'd40
    );

    state_rx_within_valid_range : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_rx <= 6'd40
    );

    // -------------------------------------------------------------------------
    // Counter validity
    // -------------------------------------------------------------------------

    count_tx_never_exceeds_three : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_tx <= 2'd3
    );

    count_rx_never_exceeds_three : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_rx <= 2'd3
    );

    count_send_data_never_overflow_normal : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_send_data <= 12'd4095
    );

    count_receive_data_never_overflow_normal : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.count_receive_data <= 12'd4095
    );

    // -------------------------------------------------------------------------
    // FSM sequential update
    // -------------------------------------------------------------------------

    state_tx_updates_from_next_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_tx === $past(module_i2c.next_state_tx)
    );

    state_rx_updates_from_next_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        module_i2c.state_rx === $past(module_i2c.next_state_rx)
    );

    // -------------------------------------------------------------------------
    // TX FSM IDLE conditions
    // -------------------------------------------------------------------------

    tx_idle_stays_idle_when_both_config_bits_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0 &&
         DATA_CONFIG_REG[0] == 1'b0 &&
         DATA_CONFIG_REG[1] == 1'b0)
        |=> (module_i2c.state_tx === 6'd0)
    );

    tx_idle_stays_idle_when_error_condition : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0 &&
         DATA_CONFIG_REG[0] == 1'b1 &&
         DATA_CONFIG_REG[1] == 1'b1)
        |=> (module_i2c.state_tx === 6'd0)
    );

    tx_idle_only_moves_to_start_when_enabled : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0) |=>
        (module_i2c.state_tx === 6'd0 || module_i2c.state_tx === 6'd1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: fifo_tx_rd_en deasserts in IDLE
    // -------------------------------------------------------------------------

    fifo_tx_rd_en_low_when_tx_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0) |=> (fifo_tx_rd_en === 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX FSM STOP: transitions to IDLE when counter reaches threshold
    // -------------------------------------------------------------------------

    tx_stop_transitions_to_idle_on_completion : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd40 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM STOP: BR_CLK_O is high
    // -------------------------------------------------------------------------

    br_clk_o_high_in_stop_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd40) |=> (module_i2c.BR_CLK_O === 1'b1)
    );

    // -------------------------------------------------------------------------
    // TX FSM: START only reachable from IDLE
    // -------------------------------------------------------------------------

    tx_start_only_entered_from_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        $rose(module_i2c.state_tx === 6'd1) |->
        $past(module_i2c.state_tx === 6'd0)
    );

    // -------------------------------------------------------------------------
    // TX FSM: DELAY_BYTES deasserts fifo_tx_rd_en
    // -------------------------------------------------------------------------

    fifo_tx_rd_en_low_in_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd38) |=> (fifo_tx_rd_en === 1'b0)
    );

    // -------------------------------------------------------------------------
    // TX FSM NACK: valid next states
    // -------------------------------------------------------------------------

    tx_nack_transitions_to_valid_state : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd39 &&
         module_i2c.count_send_data >= DATA_CONFIG_REG[13:2] * 2'd2)
        |=> (module_i2c.state_tx === 6'd2  ||
             module_i2c.state_tx === 6'd11 ||
             module_i2c.state_tx === 6'd20 ||
             module_i2c.state_tx === 6'd29)
    );

    // -------------------------------------------------------------------------
    // RX FSM IDLE conditions
    // -------------------------------------------------------------------------

    rx_idle_stays_idle_when_both_config_bits_zero : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd0 &&
         DATA_CONFIG_REG[0] == 1'b0 &&
         DATA_CONFIG_REG[1] == 1'b0)
        |=> (module_i2c.state_rx === 6'd0)
    );

    rx_idle_stays_idle_when_error_condition : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd0 &&
         DATA_CONFIG_REG[0] == 1'b1 &&
         DATA_CONFIG_REG[1] == 1'b1)
        |=> (module_i2c.state_rx === 6'd0)
    );

    // -------------------------------------------------------------------------
    // RX FSM STOP: transitions to IDLE on completion
    // -------------------------------------------------------------------------

    rx_stop_transitions_to_idle_on_completion : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd40 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx === 6'd0)
    );

    // -------------------------------------------------------------------------
    // RX FSM STOP: fifo_rx_wr_en deasserts
    // -------------------------------------------------------------------------

    fifo_rx_wr_en_low_after_rx_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd40) |=> (fifo_rx_wr_en === 1'b0)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA: high when RX is in any RESPONSE state
    // -------------------------------------------------------------------------

    enable_sda_high_when_rx_in_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd10) |-> (ENABLE_SDA === 1'b1)
    );

    enable_sda_high_when_rx_in_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd19) |-> (ENABLE_SDA === 1'b1)
    );

    enable_sda_high_when_rx_in_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd28) |-> (ENABLE_SDA === 1'b1)
    );

    enable_sda_high_when_rx_in_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd37) |-> (ENABLE_SDA === 1'b1)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SDA: low when TX is in any RESPONSE state (and RX is not)
    // -------------------------------------------------------------------------

    enable_sda_low_when_tx_in_response_cin_only : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd10 &&
         module_i2c.state_rx !== 6'd10 &&
         module_i2c.state_rx !== 6'd19 &&
         module_i2c.state_rx !== 6'd28 &&
         module_i2c.state_rx !== 6'd37)
        |-> (ENABLE_SDA === 1'b0)
    );

    enable_sda_low_when_tx_in_response_address_only : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd19 &&
         module_i2c.state_rx !== 6'd10 &&
         module_i2c.state_rx !== 6'd19 &&
         module_i2c.state_rx !== 6'd28 &&
         module_i2c.state_rx !== 6'd37)
        |-> (ENABLE_SDA === 1'b0)
    );

    enable_sda_low_when_tx_in_response_data0_only : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd28 &&
         module_i2c.state_rx !== 6'd10 &&
         module_i2c.state_rx !== 6'd19 &&
         module_i2c.state_rx !== 6'd28 &&
         module_i2c.state_rx !== 6'd37)
        |-> (ENABLE_SDA === 1'b0)
    );

    enable_sda_low_when_tx_in_response_data1_only : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd37 &&
         module_i2c.state_rx !== 6'd10 &&
         module_i2c.state_rx !== 6'd19 &&
         module_i2c.state_rx !== 6'd28 &&
         module_i2c.state_rx !== 6'd37)
        |-> (ENABLE_SDA === 1'b0)
    );

    // -------------------------------------------------------------------------
    // ENABLE_SCL: high when TX is in any RESPONSE state
    // -------------------------------------------------------------------------

    enable_scl_high_when_tx_in_response_cin : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd10) |-> (ENABLE_SCL === 1'b1)
    );

    enable_scl_high_when_tx_in_response_address : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd19) |-> (ENABLE_SCL === 1'b1)
    );

    enable_scl_high_when_tx_in_response_data0 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd28) |-> (ENABLE_SCL === 1'b1)
    );

    enable_scl_high_when_tx_in_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd37) |-> (ENABLE_SCL === 1'b1)
    );

    // -------------------------------------------------------------------------
    // Timeout counter: resets when not in IDLE
    // -------------------------------------------------------------------------

    count_timeout_resets_when_not_in_tx_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx !== 6'd0) |=> (module_i2c.count_timeout === 12'd0)
    );

    // -------------------------------------------------------------------------
    // Timeout counter: increments only when SDA and SCL are both low in IDLE
    // -------------------------------------------------------------------------

    count_timeout_increments_on_sda_scl_low_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0 &&
         SDA === 1'b0 &&
         SCL === 1'b0 &&
         module_i2c.count_timeout <= TIMEOUT_TX)
        |=> (module_i2c.count_timeout === $past(module_i2c.count_timeout) + 12'd1)
    );

    // -------------------------------------------------------------------------
    // Timeout counter: stays zero if SDA or SCL not both low in IDLE
    // -------------------------------------------------------------------------

    count_timeout_no_increment_when_lines_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd0 &&
         !(SDA === 1'b0 && SCL === 1'b0))
        |=> (module_i2c.count_timeout === 12'd0)
    );

    // -------------------------------------------------------------------------
    // TX linear state progression: within a byte send, state increments by 1
    // -------------------------------------------------------------------------

    tx_controlin_1_to_2_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd2 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd3)
    );

    tx_controlin_2_to_3_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd3 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd4)
    );

    tx_controlin_8_to_response_cin_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd9 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd10)
    );

    tx_address_8_to_response_address_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd18 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd19)
    );

    tx_data0_8_to_response_data0_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd27 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd28)
    );

    tx_data1_8_to_response_data1_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd36 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_tx === 6'd37)
    );

    // -------------------------------------------------------------------------
    // TX RESPONSE states: ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------

    tx_response_cin_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd10 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx === 6'd38)
    );

    tx_response_address_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd19 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx === 6'd38)
    );

    tx_response_data0_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd28 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx === 6'd38)
    );

    tx_response_data1_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd37 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_tx === 6'd38)
    );

    // -------------------------------------------------------------------------
    // TX RESPONSE states: NACK leads to NACK state
    // -------------------------------------------------------------------------

    tx_response_cin_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd10 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_tx === 6'd39)
    );

    tx_response_address_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd19 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_tx === 6'd39)
    );

    tx_response_data0_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd28 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_tx === 6'd39)
    );

    tx_response_data1_nack_to_nack : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd37 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b1)
        |=> (module_i2c.state_tx === 6'd39)
    );

    // -------------------------------------------------------------------------
    // TX DELAY_BYTES: count_tx determines next state
    // -------------------------------------------------------------------------

    tx_delay_bytes_count0_to_address1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd38 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd0)
        |=> (module_i2c.state_tx === 6'd11)
    );

    tx_delay_bytes_count1_to_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd38 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd1)
        |=> (module_i2c.state_tx === 6'd20)
    );

    tx_delay_bytes_count2_to_data1_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd38 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd2)
        |=> (module_i2c.state_tx === 6'd29)
    );

    tx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_tx === 6'd38 &&
         module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_tx == 2'd3)
        |=> (module_i2c.state_tx === 6'd40)
    );

    // -------------------------------------------------------------------------
    // RX linear state progression
    // -------------------------------------------------------------------------

    rx_controlin_8_to_response_cin_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd9 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx === 6'd10)
    );

    rx_address_8_to_response_address_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd18 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx === 6'd19)
    );

    rx_data0_8_to_response_data0_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd27 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx === 6'd28)
    );

    rx_data1_8_to_response_data1_on_count_match : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd36 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
        |=> (module_i2c.state_rx === 6'd37)
    );

    // -------------------------------------------------------------------------
    // RX RESPONSE states: ACK leads to DELAY_BYTES
    // -------------------------------------------------------------------------

    rx_response_cin_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd10 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_rx === 6'd38)
    );

    rx_response_address_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd19 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_rx === 6'd38)
    );

    rx_response_data0_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd28 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_rx === 6'd38)
    );

    rx_response_data1_ack_to_delay_bytes : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd37 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.RESPONSE == 1'b0)
        |=> (module_i2c.state_rx === 6'd38)
    );

    // -------------------------------------------------------------------------
    // RX DELAY_BYTES: count_rx determines next state
    // -------------------------------------------------------------------------

    rx_delay_bytes_count0_to_address1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd38 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd0)
        |=> (module_i2c.state_rx === 6'd11)
    );

    rx_delay_bytes_count1_to_data0_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd38 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd1)
        |=> (module_i2c.state_rx === 6'd20)
    );

    rx_delay_bytes_count2_to_data1_1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd38 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd2)
        |=> (module_i2c.state_rx === 6'd29)
    );

    rx_delay_bytes_count3_to_stop : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (module_i2c.state_rx === 6'd38 &&
         module_i2c.count_receive_data == DATA_CONFIG_REG[13:2] &&
         module_i2c.count_rx == 2'd3)
        |=> (module_i2c.state_rx === 6'd40)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
