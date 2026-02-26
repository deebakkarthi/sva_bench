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

// Local state encoding mirroring the DUT
localparam [5:0] IDLE          = 6'd0,
                 START         = 6'd1,
                 CONTROLIN_1   = 6'd2,
                 CONTROLIN_2   = 6'd3,
                 CONTROLIN_3   = 6'd4,
                 CONTROLIN_4   = 6'd5,
                 CONTROLIN_5   = 6'd6,
                 CONTROLIN_6   = 6'd7,
                 CONTROLIN_7   = 6'd8,
                 CONTROLIN_8   = 6'd9,
                 RESPONSE_CIN  = 6'd10,
                 ADDRESS_1     = 6'd11,
                 ADDRESS_2     = 6'd12,
                 ADDRESS_3     = 6'd13,
                 ADDRESS_4     = 6'd14,
                 ADDRESS_5     = 6'd15,
                 ADDRESS_6     = 6'd16,
                 ADDRESS_7     = 6'd17,
                 ADDRESS_8     = 6'd18,
                 RESPONSE_ADDRESS = 6'd19,
                 DATA0_1       = 6'd20,
                 DATA0_2       = 6'd21,
                 DATA0_3       = 6'd22,
                 DATA0_4       = 6'd23,
                 DATA0_5       = 6'd24,
                 DATA0_6       = 6'd25,
                 DATA0_7       = 6'd26,
                 DATA0_8       = 6'd27,
                 RESPONSE_DATA0_1 = 6'd28,
                 DATA1_1       = 6'd29,
                 DATA1_2       = 6'd30,
                 DATA1_3       = 6'd31,
                 DATA1_4       = 6'd32,
                 DATA1_5       = 6'd33,
                 DATA1_6       = 6'd34,
                 DATA1_7       = 6'd35,
                 DATA1_8       = 6'd36,
                 RESPONSE_DATA1_1 = 6'd37,
                 DELAY_BYTES   = 6'd38,
                 NACK          = 6'd39,
                 STOP          = 6'd40;

// Internal references to DUT internal signals via hierarchical reference not possible in bind
// Use outputs and observable signals only

// -----------------------------------------------------------------------
// TX_EMPTY: asserted when fifo_tx_f_empty is 1
// -----------------------------------------------------------------------
tx_empty_correct: assert property (
    @(posedge PCLK)
    TX_EMPTY == fifo_tx_f_empty
);

// -----------------------------------------------------------------------
// RX_EMPTY: asserted when fifo_rx_f_empty is 1
// -----------------------------------------------------------------------
rx_empty_correct: assert property (
    @(posedge PCLK)
    RX_EMPTY == fifo_rx_f_empty
);

// -----------------------------------------------------------------------
// ERROR: asserted only when both DATA_CONFIG_REG[0] and [1] are 1
// -----------------------------------------------------------------------
error_when_both_config_bits_set: assert property (
    @(posedge PCLK)
    (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b1
);

error_not_set_otherwise: assert property (
    @(posedge PCLK)
    !(DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1) |-> ERROR == 1'b0
);

// -----------------------------------------------------------------------
// After reset, fifo_tx_rd_en should be deasserted
// -----------------------------------------------------------------------
reset_fifo_tx_rd_en: assert property (
    @(posedge PCLK)
    !PRESETn |=> (fifo_tx_rd_en == 1'b0)
);

// -----------------------------------------------------------------------
// After reset, fifo_rx_wr_en should be deasserted
// -----------------------------------------------------------------------
reset_fifo_rx_wr_en: assert property (
    @(posedge PCLK)
    !PRESETn |=> (fifo_rx_wr_en == 1'b0)
);

// -----------------------------------------------------------------------
// ENABLE_SDA: when tx state machine is in a response state, ENABLE_SDA should be 0
// (observable only through output ENABLE_SDA)
// ENABLE_SDA and ENABLE_SCL are outputs so we can check them
// -----------------------------------------------------------------------
// ENABLE_SCL implies SDA enable when in response states
enable_sda_enable_scl_not_both_zero: assert property (
    @(posedge PCLK)
    PRESETn |-> !(ENABLE_SDA == 1'b0 && ENABLE_SCL == 1'b0)
);

// -----------------------------------------------------------------------
// TX_EMPTY and RX_EMPTY cannot both be driven by same fifo
// TX_EMPTY driven by fifo_tx_f_empty, RX_EMPTY by fifo_rx_f_empty - independent
// -----------------------------------------------------------------------
tx_empty_independent_of_rx: assert property (
    @(posedge PCLK)
    TX_EMPTY == fifo_tx_f_empty && RX_EMPTY == fifo_rx_f_empty
);

// -----------------------------------------------------------------------
// When fifo_tx_f_empty is 1, TX_EMPTY must be 1
// -----------------------------------------------------------------------
tx_empty_high_when_fifo_empty: assert property (
    @(posedge PCLK)
    fifo_tx_f_empty |-> TX_EMPTY
);

// -----------------------------------------------------------------------
// When fifo_tx_f_empty is 0, TX_EMPTY must be 0
// -----------------------------------------------------------------------
tx_empty_low_when_fifo_not_empty: assert property (
    @(posedge PCLK)
    !fifo_tx_f_empty |-> !TX_EMPTY
);

// -----------------------------------------------------------------------
// When fifo_rx_f_empty is 1, RX_EMPTY must be 1
// -----------------------------------------------------------------------
rx_empty_high_when_fifo_empty: assert property (
    @(posedge PCLK)
    fifo_rx_f_empty |-> RX_EMPTY
);

// -----------------------------------------------------------------------
// When fifo_rx_f_empty is 0, RX_EMPTY must be 0
// -----------------------------------------------------------------------
rx_empty_low_when_fifo_not_empty: assert property (
    @(posedge PCLK)
    !fifo_rx_f_empty |-> !RX_EMPTY
);

// -----------------------------------------------------------------------
// ERROR is always 0 when DATA_CONFIG_REG[0] is 0
// -----------------------------------------------------------------------
error_zero_when_config0_clear: assert property (
    @(posedge PCLK)
    (DATA_CONFIG_REG[0] == 1'b0) |-> (ERROR == 1'b0)
);

// -----------------------------------------------------------------------
// ERROR is always 0 when DATA_CONFIG_REG[1] is 0
// -----------------------------------------------------------------------
error_zero_when_config1_clear: assert property (
    @(posedge PCLK)
    (DATA_CONFIG_REG[1] == 1'b0) |-> (ERROR == 1'b0)
);

// -----------------------------------------------------------------------
// ENABLE_SDA and ENABLE_SCL are valid (not X/Z) when out of reset
// -----------------------------------------------------------------------
enable_sda_valid: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(ENABLE_SDA)
);

enable_scl_valid: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(ENABLE_SCL)
);

// -----------------------------------------------------------------------
// TX_EMPTY is never unknown when out of reset
// -----------------------------------------------------------------------
tx_empty_not_unknown: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(TX_EMPTY)
);

// -----------------------------------------------------------------------
// RX_EMPTY is never unknown when out of reset
// -----------------------------------------------------------------------
rx_empty_not_unknown: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(RX_EMPTY)
);

// -----------------------------------------------------------------------
// ERROR is never unknown when out of reset
// -----------------------------------------------------------------------
error_not_unknown: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(ERROR)
);

// -----------------------------------------------------------------------
// fifo_tx_rd_en is never unknown when out of reset (1 cycle after reset)
// -----------------------------------------------------------------------
fifo_tx_rd_en_not_unknown: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(fifo_tx_rd_en)
);

// -----------------------------------------------------------------------
// fifo_rx_wr_en is never unknown when out of reset
// -----------------------------------------------------------------------
fifo_rx_wr_en_not_unknown: assert property (
    @(posedge PCLK)
    PRESETn |-> !$isunknown(fifo_rx_wr_en)
);

// -----------------------------------------------------------------------
// When ERROR is asserted, it's because both config bits are 1
// -----------------------------------------------------------------------
error_implies_both_config_bits: assert property (
    @(posedge PCLK)
    ERROR |-> (DATA_CONFIG_REG[0] == 1'b1 && DATA_CONFIG_REG[1] == 1'b1)
);

// -----------------------------------------------------------------------
// Reset deasserts fifo_tx_rd_en on next cycle
// -----------------------------------------------------------------------
reset_clears_tx_rd_en_next: assert property (
    @(posedge PCLK)
    $fell(PRESETn) |=> (fifo_tx_rd_en == 1'b0)
);

// -----------------------------------------------------------------------
// Reset deasserts fifo_rx_wr_en on next cycle
// -----------------------------------------------------------------------
reset_clears_rx_wr_en_next: assert property (
    @(posedge PCLK)
    $fell(PRESETn) |=> (fifo_rx_wr_en == 1'b0)
);

// -----------------------------------------------------------------------
// TX_EMPTY is purely combinational: stable when inputs stable
// If fifo_tx_f_empty doesn't change, TX_EMPTY doesn't change
// -----------------------------------------------------------------------
tx_empty_stable_when_input_stable: assert property (
    @(posedge PCLK)
    ($stable(fifo_tx_f_empty)) |-> ($stable(TX_EMPTY))
);

// -----------------------------------------------------------------------
// RX_EMPTY is purely combinational: stable when inputs stable
// -----------------------------------------------------------------------
rx_empty_stable_when_input_stable: assert property (
    @(posedge PCLK)
    ($stable(fifo_rx_f_empty)) |-> ($stable(RX_EMPTY))
);

// -----------------------------------------------------------------------
// ERROR is purely combinational from DATA_CONFIG_REG bits
// -----------------------------------------------------------------------
error_stable_when_config_stable: assert property (
    @(posedge PCLK)
    ($stable(DATA_CONFIG_REG[0]) && $stable(DATA_CONFIG_REG[1])) |-> $stable(ERROR)
);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
