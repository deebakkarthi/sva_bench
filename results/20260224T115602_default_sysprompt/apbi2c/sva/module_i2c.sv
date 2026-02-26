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

    // --- Combinational output correctness ---

    tx_empty_reflects_fifo_tx_f_empty : assert property (
        @(posedge PCLK) TX_EMPTY == fifo_tx_f_empty);

    rx_empty_reflects_fifo_rx_f_empty : assert property (
        @(posedge PCLK) RX_EMPTY == fifo_rx_f_empty);

    error_high_when_both_config_bits_set : assert property (
        @(posedge PCLK) (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> ERROR);

    error_low_when_config_not_error : assert property (
        @(posedge PCLK) !(DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> !ERROR);

    tx_empty_high_when_fifo_empty : assert property (
        @(posedge PCLK) fifo_tx_f_empty |-> TX_EMPTY);

    tx_empty_low_when_fifo_not_empty : assert property (
        @(posedge PCLK) !fifo_tx_f_empty |-> !TX_EMPTY);

    rx_empty_high_when_fifo_empty : assert property (
        @(posedge PCLK) fifo_rx_f_empty |-> RX_EMPTY);

    rx_empty_low_when_fifo_not_empty : assert property (
        @(posedge PCLK) !fifo_rx_f_empty |-> !RX_EMPTY);

    // --- Reset behavior ---

    reset_deasserts_fifo_tx_rd_en : assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_tx_rd_en);

    reset_deasserts_fifo_rx_wr_en : assert property (
        @(posedge PCLK) !PRESETn |=> !fifo_rx_wr_en);

    // --- fifo_rx_wr_en is never asserted (no code path sets it to 1) ---

    fifo_rx_wr_en_never_asserted : assert property (
        @(posedge PCLK) disable iff (!PRESETn) !fifo_rx_wr_en);

    // --- ENABLE_SDA / ENABLE_SCL mutual consistency ---
    // When neither FSM is in a response state, ENABLE_SCL=0 and ENABLE_SDA=1

    enable_scl_low_implies_enable_sda_high : assert property (
        @(posedge PCLK) !ENABLE_SCL |-> ENABLE_SDA);

    // --- Mode-based TX FIFO read suppression ---

    // Error config (CONFIG[0]=1, CONFIG[1]=1): TX FSM stays IDLE, no FIFO reads
    error_config_suppresses_fifo_tx_rd_en : assert property (
        @(posedge PCLK) disable iff (!PRESETn) ERROR |-> !fifo_tx_rd_en);

    // Disabled mode (CONFIG[0]=0, CONFIG[1]=0): TX FSM stays IDLE
    disabled_mode_suppresses_fifo_tx_rd_en : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |-> !fifo_tx_rd_en);

    // RX-only mode (CONFIG[0]=0, CONFIG[1]=1): TX FSM stays IDLE
    rx_only_mode_suppresses_fifo_tx_rd_en : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> !fifo_tx_rd_en);

    // --- TX FIFO read requires TX-only mode ---

    fifo_tx_rd_en_only_in_tx_mode : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        fifo_tx_rd_en |-> (DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]));

    // --- TX FIFO full or not empty required to start TX ---
    // In TX mode: if both fifo_tx_f_full=0 and fifo_tx_f_empty=1, no read can occur

    no_fifo_tx_read_when_tx_fifo_truly_empty : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!fifo_tx_f_full && fifo_tx_f_empty) |-> !fifo_tx_rd_en);

    // --- ENABLE_SCL is high only during response states (observable proxy) ---
    // When ENABLE_SCL=1 and ENABLE_SDA=0, TX FSM is in a response state
    // In that case, fifo_tx_rd_en should not be asserted
    enable_scl_high_sda_low_no_fifo_tx_read : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (ENABLE_SCL && !ENABLE_SDA) |-> !fifo_tx_rd_en);

    // --- RX FIFO write enable stays low during error or disabled mode ---

    error_config_suppresses_fifo_rx_wr_en : assert property (
        @(posedge PCLK) disable iff (!PRESETn) ERROR |-> !fifo_rx_wr_en);

    disabled_mode_suppresses_fifo_rx_wr_en : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (!DATA_CONFIG_REG[0] && !DATA_CONFIG_REG[1]) |-> !fifo_rx_wr_en);

    // --- TX and RX EMPTY are independent of each other ---

    tx_rx_empty_independence_tx_full_rx_empty : assert property (
        @(posedge PCLK) (fifo_tx_f_full && fifo_rx_f_empty) |-> (!TX_EMPTY && RX_EMPTY));

    tx_rx_empty_independence_tx_empty_rx_full : assert property (
        @(posedge PCLK) (fifo_tx_f_empty && fifo_rx_f_full) |-> (TX_EMPTY && !RX_EMPTY));

    // --- After reset release, fifo_tx_rd_en remains low until TX FSM advances ---

    fifo_tx_rd_en_stable_low_after_reset : assert property (
        @(posedge PCLK) $rose(PRESETn) |=> !fifo_tx_rd_en);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
