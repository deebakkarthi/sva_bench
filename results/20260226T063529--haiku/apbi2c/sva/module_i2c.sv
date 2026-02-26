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

TX_EMPTY_reflects_fifo_status : assert property (
	@(posedge PCLK) TX_EMPTY == fifo_tx_f_empty
);

RX_EMPTY_reflects_fifo_status : assert property (
	@(posedge PCLK) RX_EMPTY == fifo_rx_f_empty
);

ERROR_reflects_config_register : assert property (
	@(posedge PCLK) ERROR == (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1])
);

fifo_tx_rd_en_never_asserts_when_fifo_empty : assert property (
	@(posedge PCLK) fifo_tx_f_empty |-> ~fifo_tx_rd_en
);

fifo_rx_wr_en_never_asserts_when_fifo_full : assert property (
	@(posedge PCLK) fifo_rx_f_full |-> ~fifo_rx_wr_en
);

ENABLE_SDA_and_ENABLE_SCL_valid_response_states : assert property (
	@(posedge PCLK) (ENABLE_SDA || ENABLE_SCL) |-> 
	((ENABLE_SDA == 1'b1) || (ENABLE_SCL == 1'b1))
);

fifo_rx_data_in_not_updated_when_full : assert property (
	@(posedge PCLK) fifo_rx_f_full |-> ~fifo_rx_wr_en
);

config_reg_bit_0_and_1_not_both_high_except_error : assert property (
	@(posedge PCLK) (DATA_CONFIG_REG[0] && DATA_CONFIG_REG[1]) |-> (ERROR == 1'b1)
);

tx_rd_en_single_cycle_pulse : assert property (
	@(posedge PCLK) fifo_tx_rd_en |=> ~fifo_tx_rd_en [*0:10]
);

rx_wr_en_single_cycle_pulse : assert property (
	@(posedge PCLK) fifo_rx_wr_en |=> ~fifo_rx_wr_en [*0:10]
);

ENABLE_SDA_high_when_responding : assert property (
	@(posedge PCLK) (ENABLE_SDA == 1'b1) |-> (ENABLE_SDA == 1'b1)
);

endmodule

bind module_i2c module_i2c_assert module_i2c_assert_instance (.*);
