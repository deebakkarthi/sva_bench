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

chk_tx_empty_reflects_fifo : assert property (@(posedge PCLK) disable iff(!PRESETn) TX_EMPTY == fifo_tx_f_empty);

chk_rx_empty_reflects_fifo : assert property (@(posedge PCLK) disable iff(!PRESETn) RX_EMPTY == fifo_rx_f_empty);

chk_error_signal_condition : assert property (@(posedge PCLK) disable iff(!PRESETn) (ERROR == 1'b1) -> (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1));

chk_state_tx_reset_to_idle : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.state_tx == 6'd0));

chk_state_rx_reset_to_idle : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.state_rx == 6'd0));

chk_count_send_data_max_value : assert property (@(posedge PCLK) disable iff(!PRESETn) module_i2c.count_send_data <= 12'd4095);

chk_count_receive_data_max_value : assert property (@(posedge PCLK) disable iff(!PRESETn) module_i2c.count_receive_data <= 12'd4095);

chk_count_tx_valid_range : assert property (@(posedge PCLK) disable iff(!PRESETn) module_i2c.count_tx <= 2'd3);

chk_count_rx_valid_range : assert property (@(posedge PCLK) disable iff(!PRESETn) module_i2c.count_rx <= 2'd3);

chk_response_signal_is_binary : assert property (@(posedge PCLK) disable iff(!PRESETn) (module_i2c.RESPONSE == 1'b0 || module_i2c.RESPONSE == 1'b1));

chk_fifo_tx_rd_en_only_response_data1 : assert property (@(posedge PCLK) disable iff(!PRESETn) (fifo_tx_rd_en == 1'b1) -> (module_i2c.state_tx == 6'd37));

chk_fifo_tx_rd_en_is_pulse : assert property (@(posedge PCLK) disable iff(!PRESETn) (fifo_tx_rd_en == 1'b1) |=> (fifo_tx_rd_en == 1'b0));

chk_timeout_counter_reset : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.count_timeout == 12'd0));

chk_timeout_counter_limit : assert property (@(posedge PCLK) disable iff(!PRESETn) (module_i2c.state_tx == 6'd0) -> (module_i2c.count_timeout <= TIMEOUT_TX));

chk_sda_out_reset_value : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.SDA_OUT == 1'b1));

chk_br_clk_o_reset_value : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.BR_CLK_O == 1'b1));

chk_sda_out_rx_reset_value : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.SDA_OUT_RX == 1'b0));

chk_br_clk_o_rx_reset_value : assert property (@(posedge PCLK) !PRESETn |-> ##1 (module_i2c.BR_CLK_O_RX == 1'b0));

chk_enable_sda_rx_response_states : assert property (@(posedge PCLK) disable iff(!PRESETn) (module_i2c.state_rx inside {6'd10, 6'd19, 6'd28, 6'd37}) -> (ENABLE_SDA == 1'b1));

chk_enable_scl_response_states : assert property (@(posedge PCLK) disable iff(!PRESETn) ((module_i2c.state_rx inside {6'd10, 6'd19, 6'd28, 6'd37}) || (module_i2c.state_tx inside {6'd10, 6'd19, 6'd28, 6'd37})) -> (ENABLE_SCL == 1'b1));

chk_fifo_rx_wr_en_cleanup : assert property (@(posedge PCLK) disable iff(!PRESETn) (fifo_rx_wr_en == 1'b1) |=> (fifo_rx_wr_en == 1'b0));

chk_data_config_reg_stability : assert property (@(posedge PCLK) disable iff(!PRESETn) DATA_CONFIG_REG == $past(DATA_CONFIG_REG));

chk_timeout_enabled_only_in_idle : assert property (@(posedge PCLK) disable iff(!PRESETn) ((module_i2c.state_tx != 6'd0) || (SDA == 1'b1) || (SCL == 1'b1)) |=> (module_i2c.count_timeout == 12'd0));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
