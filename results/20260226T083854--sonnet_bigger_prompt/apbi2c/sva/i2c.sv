module i2c_assert(
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

// RESET_N is active-high inverse of PRESETn
reset_n_inverse: assert property (@(posedge PCLK) (i2c.RESET_N == ~PRESETn));

// TX_F_FULL is always equal to w_full
tx_f_full_eq_w_full: assert property (@(posedge PCLK) (i2c.TX_F_FULL == i2c.w_full));

// APB: PENABLE must only be asserted when PSELx is asserted
penable_requires_pselx: assert property (@(posedge PCLK) disable iff (!PRESETn) PENABLE |-> PSELx);

// APB: PENABLE should follow PSELx by one cycle (setup phase -> access phase)
pselx_then_penable: assert property (@(posedge PCLK) disable iff (!PRESETn) (PSELx && !PENABLE) |=> (PSELx));

// APB: PSLVERR should only be valid when PREADY is high
pslverr_with_pready: assert property (@(posedge PCLK) disable iff (!PRESETn) PSLVERR |-> PREADY);

// APB: PREADY should eventually be asserted after PENABLE
penable_leads_to_pready: assert property (@(posedge PCLK) disable iff (!PRESETn) (PSELx && PENABLE) |-> ##[0:16] PREADY);

// When PRESETn is deasserted (low), RESET_N should be high
reset_n_high_on_preset_low: assert property (@(posedge PCLK) (!PRESETn) |-> i2c.RESET_N);

// When PRESETn is asserted (high), RESET_N should be low
reset_n_low_on_preset_high: assert property (@(posedge PCLK) PRESETn |-> !i2c.RESET_N);

// TX_WRITE_ENA wire connection to FIFO TX and APB must be consistent
tx_write_ena_stable: assert property (@(posedge PCLK) disable iff (!PRESETn) $stable(i2c.TX_WRITE_ENA) || PSELx);

// RX_RD_EN wire connection consistency check: only driven when bus is active
rx_rd_en_with_pselx: assert property (@(posedge PCLK) disable iff (!PRESETn) i2c.RX_RD_EN |-> PSELx);

// TX data in should be stable during a write transaction
tx_data_stable_during_write: assert property (@(posedge PCLK) disable iff (!PRESETn) (PSELx && PENABLE && PWRITE && !PREADY) |-> $stable(i2c.TX_DATA_IN));

// REGISTER_CONFIG and TIMEOUT_CONFIG should be stable when no APB transaction is ongoing
config_stable_no_transaction: assert property (@(posedge PCLK) disable iff (!PRESETn) (!PSELx) |=> $stable(i2c.REGISTER_CONFIG));

timeout_stable_no_transaction: assert property (@(posedge PCLK) disable iff (!PRESETn) (!PSELx) |=> $stable(i2c.TIMEOUT_CONFIG));

// After reset deassertion, PREADY should not be permanently stuck high without a valid transaction
pready_not_stuck_without_transaction: assert property (@(posedge PCLK) disable iff (!PRESETn) (!PSELx && !PENABLE) |-> !PREADY);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
