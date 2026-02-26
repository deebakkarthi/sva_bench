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

    // TX_EMPTY is a direct reflection of the TX FIFO empty flag
    tx_empty_reflects_fifo_tx_empty : assert property (@(posedge PCLK)
        TX_EMPTY == fifo_tx_f_empty);

    // RX_EMPTY is a direct reflection of the RX FIFO empty flag
    rx_empty_reflects_fifo_rx_empty : assert property (@(posedge PCLK)
        RX_EMPTY == fifo_rx_f_empty);

    // ERROR is asserted only when both config bits [0] and [1] are set (invalid mode)
    error_only_when_both_config_bits_set : assert property (@(posedge PCLK)
        ERROR == (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]));

    // After reset, fifo_tx_rd_en must be deasserted
    fifo_tx_rd_en_cleared_on_reset : assert property (@(posedge PCLK)
        !PRESETn |=> !fifo_tx_rd_en);

    // After reset, fifo_rx_wr_en must be deasserted
    fifo_rx_wr_en_cleared_on_reset : assert property (@(posedge PCLK)
        !PRESETn |=> !fifo_rx_wr_en);

    // In error mode (both config bits set), TX read enable must not be asserted
    no_tx_read_in_error_mode : assert property (@(posedge PCLK)
        ERROR |-> !fifo_tx_rd_en);

    // In error mode, RX write enable must not be asserted
    no_rx_write_in_error_mode : assert property (@(posedge PCLK)
        ERROR |-> !fifo_rx_wr_en);

    // When RX FIFO is full, the core must not assert RX write enable
    no_rx_write_when_rx_fifo_full : assert property (@(posedge PCLK)
        fifo_rx_f_full |-> !fifo_rx_wr_en);

    // TX read enable and RX write enable are never simultaneously asserted
    // (the TX and RX state machines operate independently and cannot overlap these signals)
    tx_rd_and_rx_wr_mutually_exclusive : assert property (@(posedge PCLK)
        !(fifo_tx_rd_en && fifo_rx_wr_en));

    // When module is disabled (DATA_CONFIG_REG[0]==0 and DATA_CONFIG_REG[1]==0),
    // no TX FIFO reads should occur
    no_tx_read_when_disabled : assert property (@(posedge PCLK)
        (!DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |-> !fifo_tx_rd_en);

    // TX_EMPTY and RX_EMPTY can both be high (both FIFOs empty is a valid idle state)
    // but neither should be driven by anything other than the FIFO flags:
    // TX_EMPTY high does not prevent RX_EMPTY from being independent
    tx_empty_independent_of_rx_empty : assert property (@(posedge PCLK)
        TX_EMPTY == fifo_tx_f_empty && RX_EMPTY == fifo_rx_f_empty);

    // After reset, the TX FIFO read enable stays deasserted for at least two cycles
    fifo_tx_rd_en_held_low_after_reset : assert property (@(posedge PCLK)
        !PRESETn |=> !fifo_tx_rd_en ##1 !fifo_tx_rd_en);

endmodule

bind module_i2c module_i2c_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) module_i2c_assert_instance (.*);
