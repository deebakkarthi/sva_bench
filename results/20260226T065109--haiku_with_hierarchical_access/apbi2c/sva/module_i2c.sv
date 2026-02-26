module module_i2c_assert#(
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

a_reset_tx_state_idle : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_tx == 6'd0));

a_reset_rx_state_idle : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.state_rx == 6'd0));

a_reset_tx_counter_zero : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_send_data == 12'd0));

a_reset_rx_counter_zero : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_receive_data == 12'd0));

a_reset_sda_output_high : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.SDA_OUT == 1'b1));

a_reset_clock_output_high : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.BR_CLK_O == 1'b1));

a_reset_tx_byte_count : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_tx == 2'd0));

a_reset_rx_byte_count : assert property (@(posedge PCLK) !PRESETn |=> (module_i2c.count_rx == 2'd0));

a_tx_empty_matches_fifo : assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

a_rx_empty_matches_fifo : assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

a_error_signal_reflects_config : assert property (@(posedge PCLK) 
    ERROR == (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]));

a_no_tx_read_when_empty : assert property (@(posedge PCLK) 
    disable iff (!PRESETn) 
    (fifo_tx_f_empty == 1'b1) |-> (fifo_tx_rd_en == 1'b0));

a_tx_counter_bounded : assert property (@(posedge PCLK) 
    (module_i2c.count_send_data <= DATA_CONFIG_REG[13:2]));

a_rx_counter_bounded : assert property (@(posedge PCLK) 
    (module_i2c.count_receive_data <= DATA_CONFIG_REG[13:2]));

a_tx_byte_counter_range : assert property (@(posedge PCLK) 
    (module_i2c.count_tx <= 2'd3));

a_rx_byte_counter_range : assert property (@(posedge PCLK) 
    (module_i2c.count_rx <= 2'd3));

a_timeout_counter_bounded : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    (module_i2c.count_timeout <= TIMEOUT_TX));

a_tx_counter_resets_at_max : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    ((module_i2c.count_send_data == DATA_CONFIG_REG[13:2]) && (module_i2c.state_tx != 6'd0))
    |=> (module_i2c.count_send_data == 12'd0));

a_rx_counter_resets_at_max : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    ((module_i2c.count_receive_data == DATA_CONFIG_REG[13:2]) && (module_i2c.state_rx != 6'd0))
    |=> (module_i2c.count_receive_data == 12'd0));

a_idle_to_start_transition : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    ((module_i2c.state_tx == 6'd0) && DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1] && !fifo_tx_f_empty)
    |-> ##[1:20] (module_i2c.state_tx != 6'd0));

a_no_rx_write_when_full : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    (fifo_rx_f_full == 1'b1) |-> (fifo_rx_wr_en == 1'b0));

a_enable_sda_in_rx_response : assert property (@(posedge PCLK) 
    (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || 
     module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37)
    |-> (ENABLE_SDA == 1'b1));

a_enable_sda_low_in_tx_response : assert property (@(posedge PCLK) 
    (module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || 
     module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37)
    |-> (ENABLE_SDA == 1'b0));

a_enable_scl_in_response : assert property (@(posedge PCLK) 
    ((module_i2c.state_tx == 6'd10 || module_i2c.state_tx == 6'd19 || 
      module_i2c.state_tx == 6'd28 || module_i2c.state_tx == 6'd37) ||
     (module_i2c.state_rx == 6'd10 || module_i2c.state_rx == 6'd19 || 
      module_i2c.state_rx == 6'd28 || module_i2c.state_rx == 6'd37))
    |-> (ENABLE_SCL == 1'b1));

a_response_only_in_valid_states : assert property (@(posedge PCLK) 
    ((module_i2c.RESPONSE == 1'b0) || (module_i2c.RESPONSE == 1'b1)) ->
    ((module_i2c.state_tx >= 6'd10 && module_i2c.state_tx <= 6'd40) ||
     (module_i2c.state_rx >= 6'd10 && module_i2c.state_rx <= 6'd40)));

a_timeout_resets_on_line_release : assert property (@(posedge PCLK) 
    disable iff (!PRESETn)
    ((module_i2c.state_tx != 6'd0) || (SDA == 1'b1) || (SCL == 1'b1))
    |=> (module_i2c.count_timeout == 12'd0));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
