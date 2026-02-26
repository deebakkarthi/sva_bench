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
    inout SDA,
    inout SCL
);

    // TX_EMPTY is always exactly equal to fifo_tx_f_empty (combinational assignment)
    tx_empty_eq_fifo_tx_f_empty : assert property (@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

    // RX_EMPTY is always exactly equal to fifo_rx_f_empty (combinational assignment)
    rx_empty_eq_fifo_rx_f_empty : assert property (@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

    // ERROR is asserted if and only if both DATA_CONFIG_REG[0] and DATA_CONFIG_REG[1] are set
    error_iff_both_config_bits_set : assert property (@(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] & DATA_CONFIG_REG[1]));

    // ERROR is deasserted when DATA_CONFIG_REG[0] is low
    error_clear_when_config0_low : assert property (@(posedge PCLK) !DATA_CONFIG_REG[0] |-> !ERROR);

    // ERROR is deasserted when DATA_CONFIG_REG[1] is low
    error_clear_when_config1_low : assert property (@(posedge PCLK) !DATA_CONFIG_REG[1] |-> !ERROR);

    // TX_EMPTY is high when TX FIFO is empty
    tx_empty_high_when_fifo_empty : assert property (@(posedge PCLK) fifo_tx_f_empty |-> TX_EMPTY);

    // TX_EMPTY is low when TX FIFO is not empty
    tx_empty_low_when_fifo_not_empty : assert property (@(posedge PCLK) !fifo_tx_f_empty |-> !TX_EMPTY);

    // RX_EMPTY is high when RX FIFO is empty
    rx_empty_high_when_fifo_empty : assert property (@(posedge PCLK) fifo_rx_f_empty |-> RX_EMPTY);

    // RX_EMPTY is low when RX FIFO is not empty
    rx_empty_low_when_fifo_not_empty : assert property (@(posedge PCLK) !fifo_rx_f_empty |-> !RX_EMPTY);

    // In transmit mode only, ERROR is deasserted
    tx_mode_no_error : assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b0) |-> !ERROR);

    // In receive mode only, ERROR is deasserted
    rx_mode_no_error : assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b1) |-> !ERROR);

    // In idle/disabled mode, ERROR is deasserted
    idle_mode_no_error : assert property (@(posedge PCLK) (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |-> !ERROR);

    // After synchronous reset, fifo_tx_rd_en must be deasserted on the following cycle
    reset_deasserts_fifo_tx_rd_en : assert property (@(posedge PCLK) !PRESETn |=> !fifo_tx_rd_en);

    // After synchronous reset, fifo_rx_wr_en must be deasserted on the following cycle
    reset_deasserts_fifo_rx_wr_en : assert property (@(posedge PCLK) !PRESETn |=> !fifo_rx_wr_en);

    // ENABLE_SDA and ENABLE_SCL cannot both be low simultaneously after reset
    enable_sda_and_scl_not_both_low : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !(ENABLE_SDA == 1'b0 && ENABLE_SCL == 1'b0));

    // When ENABLE_SDA is low (TX FSM in response state), ENABLE_SCL must be high
    enable_sda_low_implies_enable_scl_high : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !ENABLE_SDA |-> ENABLE_SCL);

    // When ENABLE_SCL is low (neither FSM in response state), ENABLE_SDA must be high
    enable_scl_low_implies_enable_sda_high : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !ENABLE_SCL |-> ENABLE_SDA);

    // TX_EMPTY output is never unknown or high-impedance
    tx_empty_never_unknown : assert property (@(posedge PCLK) !$isunknown(TX_EMPTY));

    // RX_EMPTY output is never unknown or high-impedance
    rx_empty_never_unknown : assert property (@(posedge PCLK) !$isunknown(RX_EMPTY));

    // ERROR output is never unknown or high-impedance
    error_never_unknown : assert property (@(posedge PCLK) !$isunknown(ERROR));

    // ENABLE_SDA is never unknown or high-impedance after reset
    enable_sda_never_unknown_after_reset : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !$isunknown(ENABLE_SDA));

    // ENABLE_SCL is never unknown or high-impedance after reset
    enable_scl_never_unknown_after_reset : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !$isunknown(ENABLE_SCL));

    // fifo_tx_rd_en is never unknown or high-impedance after reset
    fifo_tx_rd_en_never_unknown_after_reset : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !$isunknown(fifo_tx_rd_en));

    // fifo_rx_wr_en is never unknown or high-impedance after reset
    fifo_rx_wr_en_never_unknown_after_reset : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !$isunknown(fifo_rx_wr_en));

    // fifo_tx_rd_en is a single-cycle pulse: once asserted it must deassert the next cycle
    fifo_tx_rd_en_single_cycle_pulse : assert property (@(posedge PCLK) disable iff (!PRESETn)
        fifo_tx_rd_en |=> !fifo_tx_rd_en);

    // fifo_rx_wr_en remains deasserted after reset (never driven high in current implementation)
    fifo_rx_wr_en_remains_low_after_reset : assert property (@(posedge PCLK) disable iff (!PRESETn)
        !fifo_rx_wr_en);

    // When fifo_tx_rd_en is asserted, TX FIFO must not have been empty (data was being read)
    fifo_tx_rd_en_requires_non_empty_fifo : assert property (@(posedge PCLK) disable iff (!PRESETn)
        $rose(fifo_tx_rd_en) |-> $past(!fifo_tx_f_empty));

    // When both config bits are 0 (all disabled), fifo_tx_rd_en should not be asserted
    disabled_mode_no_tx_rd_en : assert property (@(posedge PCLK) disable iff (!PRESETn)
        (DATA_CONFIG_REG[0] == 1'b0 && DATA_CONFIG_REG[1] == 1'b0) |-> !fifo_tx_rd_en);

    // When ERROR is active (both config bits set), fifo_tx_rd_en should not be asserted
    error_mode_no_tx_rd_en : assert property (@(posedge PCLK) disable iff (!PRESETn)
        (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> !fifo_tx_rd_en);

    // ENABLE_SDA must be boolean (0 or 1, not X/Z) at all times after reset
    enable_sda_is_binary : assert property (@(posedge PCLK) disable iff (!PRESETn)
        (ENABLE_SDA === 1'b0 || ENABLE_SDA === 1'b1));

    // ENABLE_SCL must be boolean (0 or 1, not X/Z) at all times after reset
    enable_scl_is_binary : assert property (@(posedge PCLK) disable iff (!PRESETn)
        (ENABLE_SCL === 1'b0 || ENABLE_SCL === 1'b1));

    // TX_EMPTY must be boolean (0 or 1, not X/Z) at all times
    tx_empty_is_binary : assert property (@(posedge PCLK)
        (TX_EMPTY === 1'b0 || TX_EMPTY === 1'b1));

    // RX_EMPTY must be boolean (0 or 1, not X/Z) at all times
    rx_empty_is_binary : assert property (@(posedge PCLK)
        (RX_EMPTY === 1'b0 || RX_EMPTY === 1'b1));

    // ERROR must be boolean (0 or 1, not X/Z) at all times
    error_is_binary : assert property (@(posedge PCLK)
        (ERROR === 1'b0 || ERROR === 1'b1));

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
