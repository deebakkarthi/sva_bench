module i2c_assert (
    input PCLK,
    input PRESETn,
    input [31:0] PADDR,
    input [31:0] PWDATA,
    input PWRITE,
    input PSELx,
    input PENABLE,
    input PREADY,
    input PSLVERR,
    input INT_RX,
    input INT_TX,
    input [31:0] PRDATA,
    input SDA_ENABLE,
    input SCL_ENABLE,
    input SDA,
    input SCL
);

// RESET_N is active-high inversion of PRESETn
reset_n_is_inverted_presetn : assert property (
    @(posedge PCLK)
    (i2c.RESET_N == ~PRESETn)
);

// TX_F_FULL is directly assigned from w_full
tx_f_full_eq_w_full : assert property (
    @(posedge PCLK)
    (i2c.TX_F_FULL == i2c.w_full)
);

// TX FIFO resets when PRESETn is deasserted
tx_fifo_reset_wr_ptr_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_TX.wr_ptr == 4'd0)
);

tx_fifo_reset_rd_ptr_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_TX.rd_ptr == 4'd0)
);

tx_fifo_reset_counter_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_TX.counter == 4'd0)
);

// RX FIFO resets when PRESETn is deasserted
rx_fifo_reset_wr_ptr_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_RX.wr_ptr == 4'd0)
);

rx_fifo_reset_rd_ptr_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_RX.rd_ptr == 4'd0)
);

rx_fifo_reset_counter_on_presetn_low : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.DUT_FIFO_RX.counter == 4'd0)
);

// TX FIFO write enable driven by APB WR_ENA
tx_write_ena_from_apb_wr_ena : assert property (
    @(posedge PCLK)
    (i2c.TX_WRITE_ENA == i2c.DUT_APB.WR_ENA)
);

// TX FIFO data input driven by APB WRITE_DATA_ON_TX
tx_data_in_from_apb_write_data : assert property (
    @(posedge PCLK)
    (i2c.TX_DATA_IN == i2c.DUT_APB.WRITE_DATA_ON_TX)
);

// RX FIFO read enable driven by APB RD_ENA
rx_rd_en_from_apb_rd_ena : assert property (
    @(posedge PCLK)
    (i2c.RX_RD_EN == i2c.DUT_APB.RD_ENA)
);

// APB READ_DATA_ON_RX comes from RX FIFO data_out
rx_data_out_to_apb_read_data : assert property (
    @(posedge PCLK)
    (i2c.RX_DATA_OUT == i2c.DUT_APB.READ_DATA_ON_RX)
);

// PRDATA reflects RX FIFO data output (through APB)
prdata_from_rx_fifo_data_out : assert property (
    @(posedge PCLK)
    (PRDATA == i2c.RX_DATA_OUT)
);

// REGISTER_CONFIG from APB to module_i2c
config_reg_routing : assert property (
    @(posedge PCLK)
    (i2c.REGISTER_CONFIG == i2c.DUT_APB.INTERNAL_I2C_REGISTER_CONFIG)
);

// TIMEOUT_CONFIG from APB to module_i2c
timeout_config_routing : assert property (
    @(posedge PCLK)
    (i2c.TIMEOUT_CONFIG == i2c.DUT_APB.INTERNAL_I2C_REGISTER_TIMEOUT)
);

// PSLVERR is driven by internal error wire
pslverr_driven_by_error_wire : assert property (
    @(posedge PCLK)
    (PSLVERR == i2c.error)
);

// INT_TX is driven by internal tx_empty wire
int_tx_driven_by_tx_empty : assert property (
    @(posedge PCLK)
    (INT_TX == i2c.tx_empty)
);

// INT_RX is driven by internal rx_empty wire
int_rx_driven_by_rx_empty : assert property (
    @(posedge PCLK)
    (INT_RX == i2c.rx_empty)
);

// APB TX_EMPTY input is connected to internal tx_empty wire
apb_tx_empty_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_APB.TX_EMPTY == i2c.tx_empty)
);

// APB RX_EMPTY input is connected to internal rx_empty wire
apb_rx_empty_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_APB.RX_EMPTY == i2c.rx_empty)
);

// APB ERROR input is connected to internal error wire
apb_error_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_APB.ERROR == i2c.error)
);

// TX FIFO f_empty connected to TX_F_EMPTY wire
tx_fifo_f_empty_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_TX.f_empty == i2c.TX_F_EMPTY)
);

// RX FIFO f_empty connected to RX_F_EMPTY wire
rx_fifo_f_empty_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_RX.f_empty == i2c.RX_F_EMPTY)
);

// RX FIFO f_full connected to RX_F_FULL wire
rx_fifo_f_full_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_RX.f_full == i2c.RX_F_FULL)
);

// TX FIFO f_full connected to TX_F_FULL wire (via w_full)
tx_fifo_f_full_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_TX.f_full == i2c.TX_F_FULL)
);

// TX FIFO data_out connected to TX_DATA_OUT wire
tx_fifo_data_out_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_TX.data_out == i2c.TX_DATA_OUT)
);

// RX FIFO data_out connected to RX_DATA_OUT wire
rx_fifo_data_out_connection : assert property (
    @(posedge PCLK)
    (i2c.DUT_FIFO_RX.data_out == i2c.RX_DATA_OUT)
);

// TX FIFO write cannot happen when TX is full (APB won't write to a full FIFO)
tx_fifo_no_write_when_full : assert property (
    @(posedge PCLK)
    (i2c.TX_F_FULL && i2c.TX_WRITE_ENA && !i2c.TX_RD_EN)
    |=> (i2c.DUT_FIFO_TX.counter == $past(i2c.DUT_FIFO_TX.counter))
);

// RX FIFO no read when empty
rx_fifo_no_read_when_empty : assert property (
    @(posedge PCLK)
    (i2c.RX_F_EMPTY && i2c.RX_RD_EN && !i2c.RX_WRITE_ENA)
    |=> (i2c.DUT_FIFO_RX.counter == $past(i2c.DUT_FIFO_RX.counter))
);

// When PRESETn is deasserted REGISTER_CONFIG should reset to 0 next cycle
register_config_resets_to_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.REGISTER_CONFIG == 14'd0)
);

// When PRESETn is deasserted TIMEOUT_CONFIG should reset to 0 next cycle
timeout_config_resets_to_zero : assert property (
    @(posedge PCLK)
    (!PRESETn) |=> (i2c.TIMEOUT_CONFIG == 14'd0)
);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
