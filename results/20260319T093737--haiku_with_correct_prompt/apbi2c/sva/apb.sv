module apb_assert (
    input PCLK,
    input PRESETn,
    input PSELx,
    input PWRITE,
    input PENABLE,
    input [31:0] PADDR,
    input [31:0] PWDATA,
    input [31:0] READ_DATA_ON_RX,
    input ERROR,
    input TX_EMPTY,
    input RX_EMPTY,
    input [31:0] PRDATA,
    input [13:0] INTERNAL_I2C_REGISTER_CONFIG,
    input [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
    input [31:0] WRITE_DATA_ON_TX,
    input WR_ENA,
    input RD_ENA,
    input PREADY,
    input PSLVERR,
    input INT_RX,
    input INT_TX
);

wr_ena_logic: assert property (@(posedge PCLK) WR_ENA == (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx));

rd_ena_logic: assert property (@(posedge PCLK) RD_ENA == (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx));

pready_logic: assert property (@(posedge PCLK) PREADY == ((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx));

write_data_passthrough: assert property (@(posedge PCLK) WRITE_DATA_ON_TX == PWDATA);

prdata_passthrough: assert property (@(posedge PCLK) PRDATA == READ_DATA_ON_RX);

pslverr_passthrough: assert property (@(posedge PCLK) PSLVERR == ERROR);

int_tx_passthrough: assert property (@(posedge PCLK) INT_TX == TX_EMPTY);

int_rx_passthrough: assert property (@(posedge PCLK) INT_RX == RX_EMPTY);

config_register_reset: assert property (@(posedge PCLK) !PRESETn |-> ##1 INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

timeout_register_reset: assert property (@(posedge PCLK) !PRESETn |-> ##1 INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

config_register_update: assert property (@(posedge PCLK) ((PADDR == 32'd8) && PSELx && PWRITE && PREADY && PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG == PWDATA[13:0]));

timeout_register_update: assert property (@(posedge PCLK) ((PADDR == 32'd12) && PSELx && PWRITE && PREADY && PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT == PWDATA[13:0]));

config_register_hold: assert property (@(posedge PCLK) (!((PADDR == 32'd8) && PSELx && PWRITE && PREADY) && PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

timeout_register_hold: assert property (@(posedge PCLK) (!((PADDR == 32'd12) && PSELx && PWRITE && PREADY) && PRESETn) |-> ##1 (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)));

endmodule

bind apb apb_assert apb_assert_instance (.*);
