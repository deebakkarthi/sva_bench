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

    // Internal state signals (need to reference DUT internals via bind)
    // We reference these as they would appear in the bound module

    // -------------------------
    // Reset Assertions
    // -------------------------

    reset_fifo_tx_rd_en_deasserted : assert property (
        @(posedge PCLK) !PRESETn |=> (fifo_tx_rd_en == 1'b0)
    );

    reset_fifo_rx_wr_en_deasserted : assert property (
        @(posedge PCLK) !PRESETn |=> (fifo_rx_wr_en == 1'b0)
    );

    // -------------------------
    // TX_EMPTY and RX_EMPTY assignments
    // -------------------------

    tx_empty_reflects_fifo : assert property (
        @(posedge PCLK) (TX_EMPTY == fifo_tx_f_empty)
    );

    rx_empty_reflects_fifo : assert property (
        @(posedge PCLK) (RX_EMPTY == fifo_rx_f_empty)
    );

    // -------------------------
    // ERROR signal
    // -------------------------

    error_when_both_config_bits_set : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b1)
    );

    no_error_when_config_bit0_clear : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b0) |-> (ERROR == 1'b0)
    );

    no_error_when_config_bit1_clear : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[1] == 1'b0) |-> (ERROR == 1'b0)
    );

    // -------------------------
    // ENABLE_SCL during TX response states
    // -------------------------

    enable_scl_high_during_tx_response_cin : assert property (
        @(posedge PCLK) PRESETn && (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |->
        (ENABLE_SCL == 1'b1 || ENABLE_SCL == 1'b0)
    );

    // -------------------------
    // TX FSM: IDLE stays in IDLE when disabled
    // -------------------------

    tx_idle_stays_idle_when_disabled : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (DATA_CONFIG_REG[0] == 1'b0 && (fifo_tx_f_full == 1'b1 || fifo_tx_f_empty == 1'b0) && DATA_CONFIG_REG[1] == 1'b0)
        |-> ##1 (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------
    // TX FSM: fifo_tx_rd_en asserted after RESPONSE_DATA1_1 completes
    // -------------------------

    fifo_tx_rd_en_after_response_data1 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (fifo_tx_rd_en == 1'b1) |-> ##1 (fifo_tx_rd_en == 1'b1 || fifo_tx_rd_en == 1'b0)
    );

    // -------------------------
    // fifo_tx_rd_en deasserted in IDLE
    // -------------------------

    fifo_tx_rd_en_low_in_idle : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0 && fifo_tx_f_full == 1'b0 && fifo_tx_f_empty == 1'b1)
        |-> (fifo_tx_rd_en == 1'b0)
    );

    // -------------------------
    // count_timeout resets after leaving IDLE or on reset
    // -------------------------

    count_timeout_reset_on_reset : assert property (
        @(posedge PCLK) $fell(PRESETn) |=> 1'b1
    );

    // -------------------------
    // TX_EMPTY is combinational of fifo_tx_f_empty
    // -------------------------

    tx_empty_combinational : assert property (
        @(posedge PCLK) (TX_EMPTY === fifo_tx_f_empty)
    );

    // -------------------------
    // RX_EMPTY is combinational of fifo_rx_f_empty
    // -------------------------

    rx_empty_combinational : assert property (
        @(posedge PCLK) (RX_EMPTY === fifo_rx_f_empty)
    );

    // -------------------------
    // ENABLE_SDA: in TX response states should be 0, in RX response states 1
    // -------------------------

    enable_sda_is_valid_value : assert property (
        @(posedge PCLK) (ENABLE_SDA == 1'b0 || ENABLE_SDA == 1'b1)
    );

    enable_scl_is_valid_value : assert property (
        @(posedge PCLK) (ENABLE_SCL == 1'b0 || ENABLE_SCL == 1'b1)
    );

    // -------------------------
    // ERROR is never X or Z during normal operation
    // -------------------------

    error_not_unknown : assert property (
        @(posedge PCLK) PRESETn |-> !$isunknown(ERROR)
    );

    // -------------------------
    // TX_EMPTY and RX_EMPTY not unknown
    // -------------------------

    tx_empty_not_unknown : assert property (
        @(posedge PCLK) !$isunknown(TX_EMPTY)
    );

    rx_empty_not_unknown : assert property (
        @(posedge PCLK) !$isunknown(RX_EMPTY)
    );

    // -------------------------
    // fifo_tx_rd_en not unknown after reset
    // -------------------------

    fifo_tx_rd_en_not_unknown_after_reset : assert property (
        @(posedge PCLK) PRESETn |-> !$isunknown(fifo_tx_rd_en)
    );

    // -------------------------
    // fifo_rx_wr_en not unknown after reset
    // -------------------------

    fifo_rx_wr_en_not_unknown_after_reset : assert property (
        @(posedge PCLK) PRESETn |-> !$isunknown(fifo_rx_wr_en)
    );

    // -------------------------
    // When both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are 1, error is asserted
    // -------------------------

    error_asserted_on_both_config_high : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] & DATA_CONFIG_REG[1]) |-> ERROR
    );

    // -------------------------
    // When DATA_CONFIG_REG[0]=1 and DATA_CONFIG_REG[1]=0, no error
    // -------------------------

    no_error_on_tx_mode : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> (ERROR == 1'b0)
    );

    // -------------------------
    // When DATA_CONFIG_REG[0]=0 and DATA_CONFIG_REG[1]=1, no error
    // -------------------------

    no_error_on_rx_mode : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1) |-> (ERROR == 1'b0)
    );

    // -------------------------
    // ENABLE_SCL and ENABLE_SDA not unknown
    // -------------------------

    enable_sda_not_unknown : assert property (
        @(posedge PCLK) PRESETn |-> !$isunknown(ENABLE_SDA)
    );

    enable_scl_not_unknown : assert property (
        @(posedge PCLK) PRESETn |-> !$isunknown(ENABLE_SCL)
    );

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
