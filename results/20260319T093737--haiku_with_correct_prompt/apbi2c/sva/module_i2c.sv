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

tx_empty_reflects_fifo_state: assert property (@(posedge PCLK) 
    TX_EMPTY == fifo_tx_f_empty);

rx_empty_reflects_fifo_state: assert property (@(posedge PCLK) 
    RX_EMPTY == fifo_rx_f_empty);

error_high_when_both_config_bits_set: assert property (@(posedge PCLK) 
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1));

error_low_when_config_not_error_state: assert property (@(posedge PCLK) 
    ~(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b0));

tx_empty_implies_fifo_empty: assert property (@(posedge PCLK) 
    (TX_EMPTY == 1'b1) |-> (fifo_tx_f_empty == 1'b1));

rx_empty_implies_fifo_empty: assert property (@(posedge PCLK) 
    (RX_EMPTY == 1'b1) |-> (fifo_rx_f_empty == 1'b1));

enable_signals_are_binary: assert property (@(posedge PCLK) 
    ((ENABLE_SDA == 1'b0) || (ENABLE_SDA == 1'b1)) && 
    ((ENABLE_SCL == 1'b0) || (ENABLE_SCL == 1'b1)));

no_simultaneous_tx_and_rx_operations: assert property (@(posedge PCLK) disable iff(!PRESETn)
    ~(fifo_tx_rd_en == 1'b1 && fifo_rx_wr_en == 1'b1));

error_state_prevents_fifo_operations: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> 
    (fifo_tx_rd_en == 1'b0 && fifo_rx_wr_en == 1'b0));

disabled_config_no_tx_read: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |-> (fifo_tx_rd_en == 1'b0));

disabled_config_no_rx_write: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |-> (fifo_rx_wr_en == 1'b0));

enable_scl_valid_during_rx: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1) |-> (ENABLE_SCL == 1'b1));

enable_sda_valid_during_rx: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1) |-> (ENABLE_SDA == 1'b1));

no_tx_operations_in_rx_mode: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1) |-> (fifo_tx_rd_en == 1'b0));

no_rx_operations_in_tx_mode: assert property (@(posedge PCLK) disable iff(!PRESETn)
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> (fifo_rx_wr_en == 1'b0));

endmodule

bind module_i2c module_i2c_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) module_i2c_assert_instance (.*);
