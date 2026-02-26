module module_i2c_sva
#(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 14
)
(
    input              PCLK,
    input              PRESETn,

    input              fifo_tx_f_full,
    input              fifo_tx_f_empty,
    input  [DWIDTH-1:0] fifo_tx_data_out,

    input              fifo_rx_f_full,
    input              fifo_rx_f_empty,
    input              fifo_rx_wr_en,
    input  [DWIDTH-1:0] fifo_rx_data_in,

    input  [AWIDTH-1:0] DATA_CONFIG_REG,
    input  [AWIDTH-1:0] TIMEOUT_TX,

    input              fifo_tx_rd_en,
    input              TX_EMPTY,
    input              RX_EMPTY,
    input              ERROR,
    input              ENABLE_SDA,
    input              ENABLE_SCL,

    inout              SDA,
    inout              SCL,
    // internal registers exposed via bind
    input  [5:0]       state_tx,
    input  [5:0]       state_rx,
    input  [11:0]      count_send_data,
    input  [11:0]      count_receive_data,
    input  [11:0]      count_timeout,
    input  [1:0]       count_tx,
    input  [1:0]       count_rx,
    input              RESPONSE
);

  // -----------------------------------------------------------------------
  // State encoding (mirrors RTL localparam)
  // -----------------------------------------------------------------------
  localparam [5:0]
    IDLE             = 6'd0,
    START            = 6'd1,
    CONTROLIN_1      = 6'd2,
    CONTROLIN_2      = 6'd3,
    CONTROLIN_3      = 6'd4,
    CONTROLIN_4      = 6'd5,
    CONTROLIN_5      = 6'd6,
    CONTROLIN_6      = 6'd7,
    CONTROLIN_7      = 6'd8,
    CONTROLIN_8      = 6'd9,
    RESPONSE_CIN     = 6'd10,
    ADDRESS_1        = 6'd11,
    ADDRESS_2        = 6'd12,
    ADDRESS_3        = 6'd13,
    ADDRESS_4        = 6'd14,
    ADDRESS_5        = 6'd15,
    ADDRESS_6        = 6'd16,
    ADDRESS_7        = 6'd17,
    ADDRESS_8        = 6'd18,
    RESPONSE_ADDRESS = 6'd19,
    DATA0_1          = 6'd20,
    DATA0_2          = 6'd21,
    DATA0_3          = 6'd22,
    DATA0_4          = 6'd23,
    DATA0_5          = 6'd24,
    DATA0_6          = 6'd25,
    DATA0_7          = 6'd26,
    DATA0_8          = 6'd27,
    RESPONSE_DATA0_1 = 6'd28,
    DATA1_1          = 6'd29,
    DATA1_2          = 6'd30,
    DATA1_3          = 6'd31,
    DATA1_4          = 6'd32,
    DATA1_5          = 6'd33,
    DATA1_6          = 6'd34,
    DATA1_7          = 6'd35,
    DATA1_8          = 6'd36,
    RESPONSE_DATA1_1 = 6'd37,
    DELAY_BYTES      = 6'd38,
    NACK             = 6'd39,
    STOP             = 6'd40;

  // -----------------------------------------------------------------------
  // TX_EMPTY mirrors fifo_tx_f_empty
  // -----------------------------------------------------------------------
  ap_tx_empty_passthrough: assert property (@(posedge PCLK)
    PRESETn |-> (TX_EMPTY == fifo_tx_f_empty)
  );

  // -----------------------------------------------------------------------
  // RX_EMPTY mirrors fifo_rx_f_empty
  // -----------------------------------------------------------------------
  ap_rx_empty_passthrough: assert property (@(posedge PCLK)
    PRESETn |-> (RX_EMPTY == fifo_rx_f_empty)
  );

  // -----------------------------------------------------------------------
  // ERROR: asserted iff both DATA_CONFIG_REG[0] and [1] are set
  // -----------------------------------------------------------------------
  ap_error_condition: assert property (@(posedge PCLK)
    PRESETn |-> (ERROR == (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]))
  );

  // -----------------------------------------------------------------------
  // Reset: TX FSM returns to IDLE
  // -----------------------------------------------------------------------
  ap_reset_state_tx: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (state_tx == IDLE)
  );

  // -----------------------------------------------------------------------
  // Reset: RX FSM returns to IDLE
  // -----------------------------------------------------------------------
  ap_reset_state_rx: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (state_rx == IDLE)
  );

  // -----------------------------------------------------------------------
  // Reset: count_send_data cleared
  // -----------------------------------------------------------------------
  ap_reset_count_send_data: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (count_send_data == 12'd0)
  );

  // -----------------------------------------------------------------------
  // Reset: count_receive_data cleared
  // -----------------------------------------------------------------------
  ap_reset_count_receive_data: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (count_receive_data == 12'd0)
  );

  // -----------------------------------------------------------------------
  // Reset: fifo_tx_rd_en deasserted
  // -----------------------------------------------------------------------
  ap_reset_fifo_tx_rd_en: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (fifo_tx_rd_en == 1'b0)
  );

  // -----------------------------------------------------------------------
  // Reset: fifo_rx_wr_en deasserted
  // -----------------------------------------------------------------------
  ap_reset_fifo_rx_wr_en: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (fifo_rx_wr_en == 1'b0)
  );

  // -----------------------------------------------------------------------
  // Reset: count_tx cleared
  // -----------------------------------------------------------------------
  ap_reset_count_tx: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (count_tx == 2'd0)
  );

  // -----------------------------------------------------------------------
  // Reset: count_rx cleared
  // -----------------------------------------------------------------------
  ap_reset_count_rx: assert property (@(posedge PCLK)
    $fell(PRESETn) |=> (count_rx == 2'd0)
  );

  // -----------------------------------------------------------------------
  // TX FSM: IDLE stays in IDLE when disabled (DATA_CONFIG_REG[0] == 0)
  // -----------------------------------------------------------------------
  ap_tx_idle_when_disabled: assert property (@(posedge PCLK)
    (PRESETn && state_tx == IDLE && !DATA_CONFIG_REG[0]) |=>
    (state_tx == IDLE)
  );

  // -----------------------------------------------------------------------
  // TX FSM: IDLE stays in IDLE when error mode (both bits set)
  // -----------------------------------------------------------------------
  ap_tx_idle_in_error_mode: assert property (@(posedge PCLK)
    (PRESETn && state_tx == IDLE &&
     DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |=>
    (state_tx == IDLE)
  );

  // -----------------------------------------------------------------------
  // TX FSM: STOP always returns to IDLE
  // -----------------------------------------------------------------------
  ap_tx_stop_to_idle: assert property (@(posedge PCLK)
    (PRESETn && state_tx == STOP &&
     count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (state_tx == IDLE)
  );

  // -----------------------------------------------------------------------
  // TX FSM: valid state encoding
  // -----------------------------------------------------------------------
  ap_tx_state_valid: assert property (@(posedge PCLK)
    PRESETn |-> state_tx inside {
      IDLE, START,
      CONTROLIN_1, CONTROLIN_2, CONTROLIN_3, CONTROLIN_4,
      CONTROLIN_5, CONTROLIN_6, CONTROLIN_7, CONTROLIN_8,
      RESPONSE_CIN,
      ADDRESS_1, ADDRESS_2, ADDRESS_3, ADDRESS_4,
      ADDRESS_5, ADDRESS_6, ADDRESS_7, ADDRESS_8,
      RESPONSE_ADDRESS,
      DATA0_1, DATA0_2, DATA0_3, DATA0_4,
      DATA0_5, DATA0_6, DATA0_7, DATA0_8,
      RESPONSE_DATA0_1,
      DATA1_1, DATA1_2, DATA1_3, DATA1_4,
      DATA1_5, DATA1_6, DATA1_7, DATA1_8,
      RESPONSE_DATA1_1,
      DELAY_BYTES, NACK, STOP}
  );

  // -----------------------------------------------------------------------
  // RX FSM: valid state encoding
  // -----------------------------------------------------------------------
  ap_rx_state_valid: assert property (@(posedge PCLK)
    PRESETn |-> state_rx inside {
      IDLE, START,
      CONTROLIN_1, CONTROLIN_2, CONTROLIN_3, CONTROLIN_4,
      CONTROLIN_5, CONTROLIN_6, CONTROLIN_7, CONTROLIN_8,
      RESPONSE_CIN,
      ADDRESS_1, ADDRESS_2, ADDRESS_3, ADDRESS_4,
      ADDRESS_5, ADDRESS_6, ADDRESS_7, ADDRESS_8,
      RESPONSE_ADDRESS,
      DATA0_1, DATA0_2, DATA0_3, DATA0_4,
      DATA0_5, DATA0_6, DATA0_7, DATA0_8,
      RESPONSE_DATA0_1,
      DATA1_1, DATA1_2, DATA1_3, DATA1_4,
      DATA1_5, DATA1_6, DATA1_7, DATA1_8,
      RESPONSE_DATA1_1,
      DELAY_BYTES, NACK, STOP}
  );

  // -----------------------------------------------------------------------
  // TX FSM: DELAY_BYTES sequences count_tx correctly
  // -----------------------------------------------------------------------
  ap_delay_bytes_tx_to_address: assert property (@(posedge PCLK)
    (PRESETn && state_tx == DELAY_BYTES &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     count_tx == 2'd0) |=> (state_tx == ADDRESS_1)
  );

  ap_delay_bytes_tx_to_data0: assert property (@(posedge PCLK)
    (PRESETn && state_tx == DELAY_BYTES &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     count_tx == 2'd1) |=> (state_tx == DATA0_1)
  );

  ap_delay_bytes_tx_to_data1: assert property (@(posedge PCLK)
    (PRESETn && state_tx == DELAY_BYTES &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     count_tx == 2'd2) |=> (state_tx == DATA1_1)
  );

  ap_delay_bytes_tx_to_stop: assert property (@(posedge PCLK)
    (PRESETn && state_tx == DELAY_BYTES &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     count_tx == 2'd3) |=> (state_tx == STOP)
  );

  // -----------------------------------------------------------------------
  // TX FSM: ACK (RESPONSE==0) in response states leads to DELAY_BYTES
  // -----------------------------------------------------------------------
  ap_response_cin_ack_to_delay: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_CIN &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b0) |=> (state_tx == DELAY_BYTES)
  );

  ap_response_addr_ack_to_delay: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_ADDRESS &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b0) |=> (state_tx == DELAY_BYTES)
  );

  ap_response_data0_ack_to_delay: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_DATA0_1 &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b0) |=> (state_tx == DELAY_BYTES)
  );

  ap_response_data1_ack_to_delay: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_DATA1_1 &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b0) |=> (state_tx == DELAY_BYTES)
  );

  // -----------------------------------------------------------------------
  // TX FSM: NACK (RESPONSE==1) in response states leads to NACK state
  // -----------------------------------------------------------------------
  ap_response_cin_nack: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_CIN &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b1) |=> (state_tx == NACK)
  );

  ap_response_addr_nack: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_ADDRESS &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b1) |=> (state_tx == NACK)
  );

  ap_response_data0_nack: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_DATA0_1 &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b1) |=> (state_tx == NACK)
  );

  ap_response_data1_nack: assert property (@(posedge PCLK)
    (PRESETn && state_tx == RESPONSE_DATA1_1 &&
     count_send_data == DATA_CONFIG_REG[13:2] &&
     RESPONSE == 1'b1) |=> (state_tx == NACK)
  );

  // -----------------------------------------------------------------------
  // ENABLE_SDA: high when state_rx is in a response phase
  // -----------------------------------------------------------------------
  ap_enable_sda_rx_response: assert property (@(posedge PCLK)
    (PRESETn && state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                                  RESPONSE_DATA0_1, RESPONSE_DATA1_1}) |->
    ENABLE_SDA
  );

  // -----------------------------------------------------------------------
  // ENABLE_SDA: low when state_tx (not state_rx) is in a response phase
  // -----------------------------------------------------------------------
  ap_enable_sda_tx_response: assert property (@(posedge PCLK)
    (PRESETn &&
     !(state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1}) &&
      (state_tx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1})) |->
    !ENABLE_SDA
  );

  // -----------------------------------------------------------------------
  // ENABLE_SCL: high during any response phase
  // -----------------------------------------------------------------------
  ap_enable_scl_response_states: assert property (@(posedge PCLK)
    (PRESETn &&
     ((state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1}) ||
      (state_tx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1}))) |->
    ENABLE_SCL
  );

  // -----------------------------------------------------------------------
  // ENABLE_SCL: low outside any response phase
  // -----------------------------------------------------------------------
  ap_enable_scl_non_response: assert property (@(posedge PCLK)
    (PRESETn &&
     !(state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1}) &&
     !(state_tx inside {RESPONSE_CIN, RESPONSE_ADDRESS,
                        RESPONSE_DATA0_1, RESPONSE_DATA1_1})) |->
    !ENABLE_SCL
  );

  // -----------------------------------------------------------------------
  // RX FSM: IDLE stays in IDLE when disabled
  // -----------------------------------------------------------------------
  ap_rx_idle_when_disabled: assert property (@(posedge PCLK)
    (PRESETn && state_rx == IDLE &&
     !DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |=>
    (state_rx == IDLE)
  );

  // -----------------------------------------------------------------------
  // RX FSM: IDLE stays in IDLE when error mode
  // -----------------------------------------------------------------------
  ap_rx_idle_in_error_mode: assert property (@(posedge PCLK)
    (PRESETn && state_rx == IDLE &&
     DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |=>
    (state_rx == IDLE)
  );

  // -----------------------------------------------------------------------
  // RX FSM: STOP always returns to IDLE
  // -----------------------------------------------------------------------
  ap_rx_stop_to_idle: assert property (@(posedge PCLK)
    (PRESETn && state_rx == STOP &&
     count_receive_data == DATA_CONFIG_REG[13:2]) |=>
    (state_rx == IDLE)
  );

  // -----------------------------------------------------------------------
  // TX and RX FSMs never both active simultaneously
  // -----------------------------------------------------------------------
  ap_tx_rx_not_both_active: assert property (@(posedge PCLK)
    PRESETn |-> !((state_tx != IDLE && state_tx != STOP) &&
                  (state_rx != IDLE && state_rx != STOP))
  );

  // -----------------------------------------------------------------------
  // count_tx stays within [0,3]
  // -----------------------------------------------------------------------
  ap_count_tx_bounded: assert property (@(posedge PCLK)
    PRESETn |-> (count_tx <= 2'd3)
  );

  // -----------------------------------------------------------------------
  // count_rx stays within [0,3]
  // -----------------------------------------------------------------------
  ap_count_rx_bounded: assert property (@(posedge PCLK)
    PRESETn |-> (count_rx <= 2'd3)
  );

  // -----------------------------------------------------------------------
  // Cover: TX FSM completes a full transaction (reaches STOP)
  // -----------------------------------------------------------------------
  cp_tx_reaches_stop: cover property (@(posedge PCLK)
    PRESETn && state_tx == STOP
  );

  // -----------------------------------------------------------------------
  // Cover: RX FSM completes a full transaction (reaches STOP)
  // -----------------------------------------------------------------------
  cp_rx_reaches_stop: cover property (@(posedge PCLK)
    PRESETn && state_rx == STOP
  );

  // -----------------------------------------------------------------------
  // Cover: a NACK is observed on the TX path
  // -----------------------------------------------------------------------
  cp_tx_nack_observed: cover property (@(posedge PCLK)
    PRESETn && state_tx == NACK
  );

  // -----------------------------------------------------------------------
  // Cover: RX FIFO write enable is asserted (data received)
  // -----------------------------------------------------------------------
  cp_rx_fifo_written: cover property (@(posedge PCLK)
    PRESETn && fifo_rx_wr_en
  );

endmodule

bind module_i2c module_i2c_sva #(
    .DWIDTH(DWIDTH),
    .AWIDTH(AWIDTH)
) i_module_i2c_sva (
    .PCLK              (PCLK),
    .PRESETn           (PRESETn),
    .fifo_tx_f_full    (fifo_tx_f_full),
    .fifo_tx_f_empty   (fifo_tx_f_empty),
    .fifo_tx_data_out  (fifo_tx_data_out),
    .fifo_rx_f_full    (fifo_rx_f_full),
    .fifo_rx_f_empty   (fifo_rx_f_empty),
    .fifo_rx_wr_en     (fifo_rx_wr_en),
    .fifo_rx_data_in   (fifo_rx_data_in),
    .DATA_CONFIG_REG   (DATA_CONFIG_REG),
    .TIMEOUT_TX        (TIMEOUT_TX),
    .fifo_tx_rd_en     (fifo_tx_rd_en),
    .TX_EMPTY          (TX_EMPTY),
    .RX_EMPTY          (RX_EMPTY),
    .ERROR             (ERROR),
    .ENABLE_SDA        (ENABLE_SDA),
    .ENABLE_SCL        (ENABLE_SCL),
    .SDA               (SDA),
    .SCL               (SCL),
    .state_tx          (state_tx),
    .state_rx          (state_rx),
    .count_send_data   (count_send_data),
    .count_receive_data(count_receive_data),
    .count_timeout     (count_timeout),
    .count_tx          (count_tx),
    .count_rx          (count_rx),
    .RESPONSE          (RESPONSE)
);
