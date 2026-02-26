module i2c_assert (
	input PCLK,
	input PRESETn,
	input [31:0] PADDR,
	input [31:0] PWDATA,
	input PWRITE,
	input PSELx,
	input PENABLE,
	output PREADY,
	output PSLVERR,
	output INT_RX,
	output INT_TX,
	output [31:0] PRDATA,
	output SDA_ENABLE,
	output SCL_ENABLE,
	inout SDA,
	inout SCL
);

// APB Protocol Assertions

// APB address must remain stable while slave is selected
apb_address_stability: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	(PSELx && $past(PSELx)) |-> (PADDR == $past(PADDR))
);

// APB write data must remain stable during write transactions
apb_write_data_stability: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	(PWRITE && PSELx && $past(PWRITE && PSELx)) |-> (PWDATA == $past(PWDATA))
);

// PREADY must be asserted during valid APB transfer
apb_ready_when_transfer_valid: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	(PSELx && PENABLE) |-> PREADY
);

// TX FIFO State Assertions

// TX FIFO full and empty signals must be mutually exclusive
tx_fifo_not_simultaneously_full_and_empty: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	~(TX_F_FULL && TX_F_EMPTY)
);

// TX FIFO must not accept writes while full
tx_fifo_no_write_when_full: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	TX_F_FULL |-> ~TX_WRITE_ENA
);

// TX FIFO must not service reads while empty
tx_fifo_no_read_when_empty: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	TX_F_EMPTY |-> ~TX_RD_EN
);

// RX FIFO State Assertions

// RX FIFO full and empty signals must be mutually exclusive
rx_fifo_not_simultaneously_full_and_empty: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	~(RX_F_FULL && RX_F_EMPTY)
);

// RX FIFO must not accept writes while full
rx_fifo_no_write_when_full: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	RX_F_FULL |-> ~RX_WRITE_ENA
);

// RX FIFO must not service reads while empty
rx_fifo_no_read_when_empty: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	RX_F_EMPTY |-> ~RX_RD_EN
);

// Signal Consistency Assertions

// TX FIFO full signal must match internal w_full
tx_full_signal_assignment: assert property (
	@(posedge PCLK)
	(TX_F_FULL == w_full)
);

// RESET_N must be inverse of PRESETn
reset_n_is_inverse_of_preset: assert property (
	@(posedge PCLK)
	(RESET_N == ~PRESETn)
);

// tx_empty flag must match TX FIFO empty status
tx_empty_signal_consistency: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	(tx_empty == TX_F_EMPTY)
);

// rx_empty flag must match RX FIFO empty status
rx_empty_signal_consistency: assert property (
	@(posedge PCLK)
	disable iff (~PRESETn)
	(rx_empty == RX_F_EMPTY)
);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
