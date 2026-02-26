module module_i2c_assert #(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 14
)
(
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

// Local parameter definitions matching the DUT
localparam [5:0] IDLE            = 6'd0,
                 START           = 6'd1,
                 CONTROLIN_1     = 6'd2,
                 CONTROLIN_2     = 6'd3,
                 CONTROLIN_3     = 6'd4,
                 CONTROLIN_4     = 6'd5,
                 CONTROLIN_5     = 6'd6,
                 CONTROLIN_6     = 6'd7,
                 CONTROLIN_7     = 6'd8,
                 CONTROLIN_8     = 6'd9,
                 RESPONSE_CIN    = 6'd10,
                 ADDRESS_1       = 6'd11,
                 ADDRESS_2       = 6'd12,
                 ADDRESS_3       = 6'd13,
                 ADDRESS_4       = 6'd14,
                 ADDRESS_5       = 6'd15,
                 ADDRESS_6       = 6'd16,
                 ADDRESS_7       = 6'd17,
                 ADDRESS_8       = 6'd18,
                 RESPONSE_ADDRESS= 6'd19,
                 DATA0_1         = 6'd20,
                 DATA0_2         = 6'd21,
                 DATA0_3         = 6'd22,
                 DATA0_4         = 6'd23,
                 DATA0_5         = 6'd24,
                 DATA0_6         = 6'd25,
                 DATA0_7         = 6'd26,
                 DATA0_8         = 6'd27,
                 RESPONSE_DATA0_1= 6'd28,
                 DATA1_1         = 6'd29,
                 DATA1_2         = 6'd30,
                 DATA1_3         = 6'd31,
                 DATA1_4         = 6'd32,
                 DATA1_5         = 6'd33,
                 DATA1_6         = 6'd34,
                 DATA1_7         = 6'd35,
                 DATA1_8         = 6'd36,
                 RESPONSE_DATA1_1= 6'd37,
                 DELAY_BYTES     = 6'd38,
                 NACK            = 6'd39,
                 STOP            = 6'd40;

// TX_EMPTY reflects fifo_tx_f_empty
tx_empty_correct: assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

// RX_EMPTY reflects fifo_rx_f_empty
rx_empty_correct: assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

// ERROR is asserted when both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are set
error_signal_correct: assert property (@(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] & DATA_CONFIG_REG[1]));

// After reset, TX state machine should be in IDLE
tx_state_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == IDLE));

// After reset, RX state machine should be in IDLE
rx_state_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == IDLE));

// After reset, fifo_tx_rd_en should be deasserted
fifo_tx_rd_en_reset: assert property (@(posedge PCLK) !PRESETn |=> (fifo_tx_rd_en == 1'b0));

// After reset, fifo_rx_wr_en should be deasserted
fifo_rx_wr_en_reset: assert property (@(posedge PCLK) !PRESETn |=> (fifo_rx_wr_en == 1'b0));

// After reset, count_send_data should be 0
count_send_data_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0));

// After reset, count_receive_data should be 0
count_receive_data_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0));

// After reset, BR_CLK_O should be 1
br_clk_o_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1));

// After reset, RESPONSE should be 0
response_reset: assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.RESPONSE == 1'b0));

// TX state machine should only be in valid states (0-40)
tx_state_valid: assert property (@(posedge PCLK) PRESETn |-> (module_i2c.state_tx <= 6'd40));

// RX state machine should only be in valid states (0-40)
rx_state_valid: assert property (@(posedge PCLK) PRESETn |-> (module_i2c.state_rx <= 6'd40));

// TX IDLE: stays IDLE if not enabled (DATA_CONFIG_REG[0]==0)
tx_idle_stays_idle_when_disabled: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |=> 
    (module_i2c.state_tx == IDLE));

// TX IDLE: stays IDLE when error condition (both bits set)
tx_idle_stays_idle_on_error: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |=> 
    (module_i2c.state_tx == IDLE));

// TX state: from IDLE can only go to IDLE or START
tx_idle_next_state: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == IDLE) |=>
    (module_i2c.state_tx == IDLE || module_i2c.state_tx == START));

// TX state: START transitions to CONTROLIN_1 or stays in START
tx_start_next_state: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == START) |=>
    (module_i2c.state_tx == START || module_i2c.state_tx == CONTROLIN_1));

// TX STOP: goes to IDLE after completion
tx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == STOP && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == IDLE));

// TX CONTROLIN_1 to CONTROLIN_2 transition
tx_controlin1_to_controlin2: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == CONTROLIN_1 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == CONTROLIN_2));

// TX CONTROLIN_8 to RESPONSE_CIN transition
tx_controlin8_to_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == CONTROLIN_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == RESPONSE_CIN));

// TX ADDRESS_8 transitions to RESPONSE_ADDRESS
tx_address8_to_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == ADDRESS_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == RESPONSE_ADDRESS));

// TX DATA0_8 transitions to RESPONSE_DATA0_1
tx_data0_8_to_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == DATA0_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == RESPONSE_DATA0_1));

// TX DATA1_8 transitions to RESPONSE_DATA1_1
tx_data1_8_to_response: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == DATA1_8 && module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_tx == RESPONSE_DATA1_1));

// RX IDLE: stays IDLE when not in receive mode
rx_idle_stays_idle_when_not_rx: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |=>
    (module_i2c.state_rx == IDLE));

// RX IDLE: stays IDLE when error
rx_idle_stays_idle_on_error: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == IDLE && DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |=>
    (module_i2c.state_rx == IDLE));

// RX state: from IDLE can only go to IDLE or START
rx_idle_next_state: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == IDLE) |=>
    (module_i2c.state_rx == IDLE || module_i2c.state_rx == START));

// RX STOP transitions to IDLE
rx_stop_to_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == STOP && module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.state_rx == IDLE));

// fifo_tx_rd_en is deasserted in IDLE
fifo_tx_rd_en_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == IDLE) |=> (fifo_tx_rd_en == 1'b0));

// ENABLE_SCL is high when in TX or RX response states
enable_scl_in_tx_response: assert property (@(posedge PCLK)
    (module_i2c.state_tx == RESPONSE_CIN ||
     module_i2c.state_tx == RESPONSE_ADDRESS ||
     module_i2c.state_tx == RESPONSE_DATA0_1 ||
     module_i2c.state_tx == RESPONSE_DATA1_1) |-> ENABLE_SCL == 1'b1);

// ENABLE_SDA is high when in RX response states
enable_sda_in_rx_response: assert property (@(posedge PCLK)
    (module_i2c.state_rx == RESPONSE_CIN ||
     module_i2c.state_rx == RESPONSE_ADDRESS ||
     module_i2c.state_rx == RESPONSE_DATA0_1 ||
     module_i2c.state_rx == RESPONSE_DATA1_1) |-> ENABLE_SDA == 1'b1);

// ENABLE_SDA is low when only in TX response states (not RX)
enable_sda_low_in_tx_response_only: assert property (@(posedge PCLK)
    ((module_i2c.state_tx == RESPONSE_CIN ||
      module_i2c.state_tx == RESPONSE_ADDRESS ||
      module_i2c.state_tx == RESPONSE_DATA0_1 ||
      module_i2c.state_tx == RESPONSE_DATA1_1) &&
     !(module_i2c.state_rx == RESPONSE_CIN ||
       module_i2c.state_rx == RESPONSE_ADDRESS ||
       module_i2c.state_rx == RESPONSE_DATA0_1 ||
       module_i2c.state_rx == RESPONSE_DATA1_1)) |-> ENABLE_SDA == 1'b0);

// ERROR is never high when DATA_CONFIG_REG[0] is low
error_not_asserted_when_disabled: assert property (@(posedge PCLK)
    DATA_CONFIG_REG[0] == 1'b0 |-> ERROR == 1'b0);

// count_tx is always <= 3 (2-bit counter)
count_tx_range: assert property (@(posedge PCLK) disable iff (!PRESETn)
    module_i2c.count_tx <= 2'd3);

// count_rx is always <= 3 (2-bit counter)
count_rx_range: assert property (@(posedge PCLK) disable iff (!PRESETn)
    module_i2c.count_rx <= 2'd3);

// When in IDLE with no activity, fifo_tx_rd_en remains 0
tx_rd_en_not_asserted_in_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == IDLE && $stable(module_i2c.state_tx)) |-> fifo_tx_rd_en == 1'b0);

// TX state: RESPONSE_CIN with ACK goes to DELAY_BYTES
tx_response_cin_ack_to_delay: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == RESPONSE_CIN &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0) |=>
    (module_i2c.state_tx == DELAY_BYTES));

// TX state: RESPONSE_CIN with NACK goes to NACK state
tx_response_cin_nack_to_nack: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == RESPONSE_CIN &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b1) |=>
    (module_i2c.state_tx == NACK));

// TX state: RESPONSE_ADDRESS with ACK goes to DELAY_BYTES
tx_response_addr_ack_to_delay: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == RESPONSE_ADDRESS &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.RESPONSE == 1'b0) |=>
    (module_i2c.state_tx == DELAY_BYTES));

// TX state: RESPONSE_DATA1_1 count_send_data resets after completing
tx_response_data1_completion: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == RESPONSE_DATA1_1 &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) |=>
    (fifo_tx_rd_en == 1'b1 || module_i2c.state_tx != RESPONSE_DATA1_1));

// count_send_data increments by 1 each clock in data states
count_send_data_increments: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == START &&
     module_i2c.count_send_data < DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.count_send_data == ($past(module_i2c.count_send_data) + 12'd1)));

// count_receive_data increments by 1 each clock in RX data states
count_receive_data_increments: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_rx == START &&
     module_i2c.count_receive_data < DATA_CONFIG_REG[13:2]) |=>
    (module_i2c.count_receive_data == ($past(module_i2c.count_receive_data) + 12'd1)));

// count_timeout resets when state_tx leaves IDLE
count_timeout_resets_on_leave_idle: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx != IDLE) |=>
    (module_i2c.count_timeout == 12'd0));

// DELAY_BYTES: count_tx increments when moving through delay
tx_delay_count_tx_increments: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == DELAY_BYTES &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx < 2'd3) |=>
    (module_i2c.count_tx == ($past(module_i2c.count_tx) + 2'd1)));

// When tx count_tx==3 and DELAY_BYTES completes, go to STOP
tx_delay_to_stop: assert property (@(posedge PCLK) disable iff (!PRESETn)
    (module_i2c.state_tx == DELAY_BYTES &&
     module_i2c.count_send_data == DATA_CONFIG_REG[13:2] &&
     module_i2c.count_tx == 2'd3) |=>
    (module_i2c.state_tx == STOP));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
