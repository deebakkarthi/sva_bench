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

tx_empty_eq_fifo_tx_f_empty : assert property (
    @(posedge PCLK)
    (TX_EMPTY == fifo_tx_f_empty)
);

rx_empty_eq_fifo_rx_f_empty : assert property (
    @(posedge PCLK)
    (RX_EMPTY == fifo_rx_f_empty)
);

error_high_when_both_config_bits_set : assert property (
    @(posedge PCLK)
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1)
);

error_low_when_not_both_config_bits_set : assert property (
    @(posedge PCLK)
    !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b0)
);

// -------------------------------------------------------------------------
// ENABLE_SDA correctness
// -------------------------------------------------------------------------

enable_sda_high_in_rx_response_states : assert property (
    @(posedge PCLK)
    (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
     module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
    |-> (ENABLE_SDA == 1'b1)
);

enable_sda_low_in_tx_response_states_only : assert property (
    @(posedge PCLK)
    (!(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
       module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
      (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
       module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37))
    |-> (ENABLE_SDA == 1'b0)
);

enable_sda_high_when_no_response_states : assert property (
    @(posedge PCLK)
    (!(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
       module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
     !(module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
       module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37))
    |-> (ENABLE_SDA == 1'b1)
);

// -------------------------------------------------------------------------
// ENABLE_SCL correctness
// -------------------------------------------------------------------------

enable_scl_high_in_rx_response_states : assert property (
    @(posedge PCLK)
    (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
     module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
    |-> (ENABLE_SCL == 1'b1)
);

enable_scl_high_in_tx_response_states_not_rx : assert property (
    @(posedge PCLK)
    (!(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
       module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
      (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
       module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37))
    |-> (ENABLE_SCL == 1'b1)
);

enable_scl_low_when_no_response_states : assert property (
    @(posedge PCLK)
    (!(module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 ||
       module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37) &&
     !(module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 ||
       module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37))
    |-> (ENABLE_SCL == 1'b0)
);

// -------------------------------------------------------------------------
// Reset assertions
// -------------------------------------------------------------------------

reset_count_send_data : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.count_send_data == 12'd0)
);

reset_state_tx_to_idle : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.state_tx == 6'd0)
);

reset_sda_out_high : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.SDA_OUT == 1'b1)
);

reset_fifo_tx_rd_en_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (fifo_tx_rd_en == 1'b0)
);

reset_count_tx_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.count_tx == 2'd0)
);

reset_br_clk_o_high : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.BR_CLK_O == 1'b1)
);

reset_response_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.RESPONSE == 1'b0)
);

reset_count_receive_data_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.count_receive_data == 12'd0)
);

reset_state_rx_to_idle : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.state_rx == 6'd0)
);

reset_sda_out_rx_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.SDA_OUT_RX == 1'b0)
);

reset_fifo_rx_wr_en_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (fifo_rx_wr_en == 1'b0)
);

reset_count_rx_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.count_rx == 2'd0)
);

reset_br_clk_o_rx_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.BR_CLK_O_RX == 1'b0)
);

reset_count_timeout_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (module_i2c.count_timeout == 12'd0)
);

// -------------------------------------------------------------------------
// FSM TX state validity
// -------------------------------------------------------------------------

state_tx_valid_range : assert property (
    @(posedge PCLK)
    (module_i2c.state_tx <= 6'd40)
);

state_rx_valid_range : assert property (
    @(posedge PCLK)
    (module_i2c.state_rx <= 6'd40)
);

// -------------------------------------------------------------------------
// FSM TX sequential state update
// -------------------------------------------------------------------------

state_tx_updates_to_next_state : assert property (
    @(posedge PCLK)
    PRESETn
    |=> (module_i2c.state_tx == $past(module_i2c.next_state_tx))
);

state_rx_updates_to_next_state : assert property (
    @(posedge PCLK)
    PRESETn
    |=> (module_i2c.state_rx == $past(module_i2c.next_state_rx))
);

// -------------------------------------------------------------------------
// TX IDLE state behavior
// -------------------------------------------------------------------------

fifo_tx_rd_en_deasserted_in_idle : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd0)
    |=> (fifo_tx_rd_en == 1'b0)
);

state_tx_stays_idle_when_error : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
    |=> (module_i2c.state_tx == 6'd0)
);

state_tx_stays_idle_when_config_disabled : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0)
    |=> (module_i2c.state_tx == 6'd0)
);

state_tx_can_only_leave_idle_to_start : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd0 &&
     module_i2c.next_state_tx != 6'd0)
    |-> (module_i2c.next_state_tx == 6'd1)
);

// -------------------------------------------------------------------------
// TX START state behavior
// -------------------------------------------------------------------------

state_tx_start_proceeds_to_controlin1 : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd1 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd2)
);

// -------------------------------------------------------------------------
// TX STOP state behavior
// -------------------------------------------------------------------------

state_tx_stop_transitions_to_idle : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd40 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_tx == 6'd0)
);

// -------------------------------------------------------------------------
// TX DELAY_BYTES state behavior
// -------------------------------------------------------------------------

fifo_tx_rd_en_deasserted_in_delay_bytes : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd38)
    |=> (fifo_tx_rd_en == 1'b0)
);

// -------------------------------------------------------------------------
// TX NACK state behavior
// -------------------------------------------------------------------------

fifo_tx_rd_en_deasserted_in_nack : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd39)
    |=> (fifo_tx_rd_en == 1'b0)
);

// -------------------------------------------------------------------------
// fifo_tx_rd_en asserted at end of RESPONSE_DATA1_1
// -------------------------------------------------------------------------

fifo_tx_rd_en_asserted_at_response_data1_1_end : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd37 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2])
    |=> (fifo_tx_rd_en == 1'b1)
);

// -------------------------------------------------------------------------
// RX STOP state: fifo_rx_wr_en deasserted
// -------------------------------------------------------------------------

fifo_rx_wr_en_deasserted_in_stop : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_rx == 6'd40)
    |=> (fifo_rx_wr_en == 1'b0)
);

// -------------------------------------------------------------------------
// count_tx and count_rx bounds
// -------------------------------------------------------------------------

count_tx_within_2bit_bounds : assert property (
    @(posedge PCLK)
    (module_i2c.count_tx <= 2'd3)
);

count_rx_within_2bit_bounds : assert property (
    @(posedge PCLK)
    (module_i2c.count_rx <= 2'd3)
);

// -------------------------------------------------------------------------
// count_timeout behavior
// -------------------------------------------------------------------------

count_timeout_resets_when_not_idle : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx != 6'd0)
    |=> (module_i2c.count_timeout == 12'd0)
);

count_timeout_resets_when_exceeds_timeout_tx : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.count_timeout > TIMEOUT_TX)
    |=> (module_i2c.count_timeout == 12'd0)
);

count_timeout_increments_only_in_idle : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx != 6'd0 &&
     module_i2c.count_timeout <= TIMEOUT_TX)
    |=> (module_i2c.count_timeout == 12'd0)
);

// -------------------------------------------------------------------------
// count_send_data and count_receive_data bounds
// -------------------------------------------------------------------------

count_send_data_within_12bit_bounds : assert property (
    @(posedge PCLK)
    (module_i2c.count_send_data <= 12'd4095)
);

count_receive_data_within_12bit_bounds : assert property (
    @(posedge PCLK)
    (module_i2c.count_receive_data <= 12'd4095)
);

// -------------------------------------------------------------------------
// TX FSM response state transitions
// -------------------------------------------------------------------------

response_cin_tx_ack_to_delay : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

response_cin_tx_nack_to_nack : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd10 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1)
    |=> (module_i2c.state_tx == 6'd39)
);

response_address_tx_ack_to_delay : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd19 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

response_address_tx_nack_to_nack : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd19 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1)
    |=> (module_i2c.state_tx == 6'd39)
);

response_data0_tx_ack_to_delay : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd28 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

response_data1_tx_ack_to_delay : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd37 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0)
    |=> (module_i2c.state_tx == 6'd38)
);

// -------------------------------------------------------------------------
// TX FSM DELAY_BYTES count_tx routing
// -------------------------------------------------------------------------

delay_bytes_tx_count0_to_address1 : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd0)
    |=> (module_i2c.state_tx == 6'd11)
);

delay_bytes_tx_count1_to_data0_1 : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd1)
    |=> (module_i2c.state_tx == 6'd20)
);

delay_bytes_tx_count2_to_data1_1 : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd2)
    |=> (module_i2c.state_tx == 6'd29)
);

delay_bytes_tx_count3_to_stop : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_tx == 6'd38 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd3)
    |=> (module_i2c.state_tx == 6'd40)
);

// -------------------------------------------------------------------------
// RX FSM IDLE stays in IDLE when no valid start condition
// -------------------------------------------------------------------------

state_rx_stays_idle_when_both_config_bits_set : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_rx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
    |=> (module_i2c.state_rx == 6'd0)
);

state_rx_stays_idle_when_config_disabled : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_rx == 6'd0 &&
     DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0)
    |=> (module_i2c.state_rx == 6'd0)
);

// -------------------------------------------------------------------------
// RX STOP transitions to IDLE
// -------------------------------------------------------------------------

state_rx_stop_transitions_to_idle : assert property (
    @(posedge PCLK)
    (PRESETn && module_i2c.state_rx == 6'd40 &&
     module_i2c.count_receive_data == DATA_CONFIG_REG[13:2])
    |=> (module_i2c.state_rx == 6'd0)
);

endmodule

bind module_i2c module_i2c_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) module_i2c_assert_instance (.*);
