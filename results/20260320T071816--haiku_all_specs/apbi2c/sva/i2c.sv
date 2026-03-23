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

reset_n_inverted_from_presetn: assert property (i2c.RESET_N == !PRESETn);

apb_pready_requires_psel_penable: assert property (@(posedge PCLK) PREADY |-> (PSELx && PENABLE));

tx_fifo_no_read_when_empty: assert property (@(posedge PCLK) disable iff (!PRESETn) i2c.TX_F_EMPTY |-> !i2c.TX_RD_EN);

rx_fifo_no_read_when_empty: assert property (@(posedge PCLK) disable iff (!PRESETn) i2c.RX_F_EMPTY |-> !i2c.RX_RD_EN);

tx_fifo_no_write_when_full: assert property (@(posedge PCLK) disable iff (!PRESETn) i2c.TX_F_FULL |-> !i2c.TX_WRITE_ENA);

rx_fifo_no_write_when_full: assert property (@(posedge PCLK) disable iff (!PRESETn) i2c.RX_F_FULL |-> !i2c.RX_WRITE_ENA);

tx_f_full_reflects_w_full: assert property (i2c.TX_F_FULL == i2c.w_full);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
