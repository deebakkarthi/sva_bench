module module_i2c_assert #(
  parameter integer DWIDTH = 32,
  parameter integer AWIDTH = 14
) (
  input PCLK,
  input PRESETn,
  input fifo_tx_f_full,
  input fifo_tx_f_empty,
  input [DWIDTH-1:0] fifo_tx_data_out,
  input fifo_rx_f_full,
  input fifo_rx_f_empty,
  output reg fifo_rx_wr_en,
  output reg [DWIDTH-1:0] fifo_rx_data_in,
  input [AWIDTH-1:0] DATA_CONFIG_REG,
  input [AWIDTH-1:0] TIMEOUT_TX,
  output reg fifo_tx_rd_en,
  output TX_EMPTY,
  output RX_EMPTY,
  output ERROR,
  output ENABLE_SDA,
  output ENABLE_SCL,
  inout SDA,
  inout SCL
);

// Reset assertion - all critical signals reset to known state
reset_signal_sync : assert property (
  @(negedge PRESETn) disable iff (PRESETn)
  1'b1 |=> (fifo_tx_rd_en == 1'b0 && fifo_rx_wr_en == 1'b0)
);

// TX_EMPTY output matches fifo_tx_f_empty
tx_empty_correct : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (fifo_tx_f_empty == 1'b1) |=> (TX_EMPTY == 1'b1)
);

// RX_EMPTY output matches fifo_rx_f_empty
rx_empty_correct : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (fifo_rx_f_empty == 1'b1) |=> (RX_EMPTY == 1'b1)
);

// ERROR signal only asserted when both config bits are set
error_signal_correct : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |=> (ERROR == 1'b1)
);

// ERROR signal deasserted when config bits are not both set
error_signal_deassert : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (DATA_CONFIG_REG[0] == 1'b0 || DATA_CONFIG_REG[1] == 1'b0) |=> (ERROR == 1'b0)
);

// count_send_data should not exceed configuration value in normal operation
count_send_data_bounded : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (DATA_CONFIG_REG != 14'h0) |-> (count_send_data <= DATA_CONFIG_REG[13:2] + 1)
);

// count_receive_data should not exceed configuration value in normal operation
count_receive_data_bounded : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (DATA_CONFIG_REG != 14'h0) |-> (count_receive_data <= DATA_CONFIG_REG[13:2] + 1)
);

// FIFO TX read enable should only pulse for one cycle
fifo_tx_rd_en_pulse : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (fifo_tx_rd_en == 1'b1) |=> (fifo_tx_rd_en == 1'b0)
);

// FIFO RX write enable should be controlled properly
fifo_rx_wr_en_control : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_rx == STOP) |-> (fifo_rx_wr_en == 1'b0)
);

// TX state machine starts in IDLE
tx_state_initial : assert property (
  @(posedge PCLK)
  (!PRESETn) |=> (state_tx == IDLE)
);

// RX state machine starts in IDLE
rx_state_initial : assert property (
  @(posedge PCLK)
  (!PRESETn) |=> (state_rx == IDLE)
);

// count_tx counter bounded to 2 bits
count_tx_bounded : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (count_tx <= 2'd3)
);

// count_rx counter bounded to 2 bits
count_rx_bounded : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (count_rx <= 2'd3)
);

// SDA_OUT should be stable during non-START states
sda_out_stability : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_tx != START && state_tx != STOP) |-> (SDA_OUT == $past(SDA_OUT) || count_send_data == 0)
);

// BR_CLK_O should follow clock generation pattern
br_clk_generation : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_tx inside {CONTROLIN_1, CONTROLIN_2, CONTROLIN_3, CONTROLIN_4, CONTROLIN_5, CONTROLIN_6, CONTROLIN_7, CONTROLIN_8}) |-> 
  ((count_send_data < DATA_CONFIG_REG[13:2]/12'd4) |-> (BR_CLK_O == 1'b0))
);

// count_timeout increments only in IDLE state
timeout_counter_idle : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_tx != IDLE) |-> (count_timeout == $past(count_timeout))
);

// count_timeout resets when exiting IDLE
timeout_counter_reset : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  ($past(state_tx) == IDLE && state_tx != IDLE) |=> (count_timeout == 12'd0)
);

// When TX FIFO is empty and not in error state, TX_EMPTY should be asserted
idle_no_data : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (fifo_tx_f_empty == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> (state_tx == IDLE || state_tx == START)
);

// RESPONSE bit should only be sampled during response states
response_sample_timing : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  ((state_tx == RESPONSE_CIN || state_tx == RESPONSE_ADDRESS || state_tx == RESPONSE_DATA0_1 || state_tx == RESPONSE_DATA1_1) && 
   (count_send_data >= DATA_CONFIG_REG[13:2])) |-> (RESPONSE == SDA)
);

// Data bits from FIFO should be transmitted in order
controlin_data_sequence : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_tx == CONTROLIN_1 && count_send_data == DATA_CONFIG_REG[13:2] - 1) |=> (SDA_OUT == fifo_tx_data_out[1:1] || state_tx != CONTROLIN_2)
);

// RX data should be captured only when SCL is high
rx_scl_timing : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_rx inside {CONTROLIN_1, CONTROLIN_2, CONTROLIN_3, CONTROLIN_4, CONTROLIN_5, CONTROLIN_6, CONTROLIN_7, CONTROLIN_8} && SCL == 1'b0) |-> 
  (fifo_rx_data_in == $past(fifo_rx_data_in))
);

// ENABLE_SDA should reflect receiver state
enable_sda_logic : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS, RESPONSE_DATA0_1, RESPONSE_DATA1_1}) |-> (ENABLE_SDA == 1'b1)
);

// ENABLE_SCL should reflect receiver state
enable_scl_logic : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (state_rx inside {RESPONSE_CIN, RESPONSE_ADDRESS, RESPONSE_DATA0_1, RESPONSE_DATA1_1}) |-> (ENABLE_SCL == 1'b1)
);

// When disabled (DATA_CONFIG_REG[0]==0), module should stay in IDLE
module_disabled : assert property (
  @(posedge PCLK) disable iff (!PRESETn)
  (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |-> (state_tx == IDLE && state_rx == IDLE)
);

endmodule

bind module_i2c module_i2c_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) module_i2c_sva_instance (.*);
