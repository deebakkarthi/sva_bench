module apb_assert(
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
			
			output [31:0] PRDATA,

			output reg [13:0] INTERNAL_I2C_REGISTER_CONFIG,
			output reg [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
			output [31:0] WRITE_DATA_ON_TX,
			output  WR_ENA,
			output  RD_ENA,
			
			output PREADY,
			output PSLVERR,

			output INT_RX,
			output INT_TX
);

// WR_ENA correctness
wr_ena_high: assert property (@(posedge PCLK)
    (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b1);

wr_ena_low: assert property (@(posedge PCLK)
    !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> WR_ENA == 1'b0);

// RD_ENA correctness
rd_ena_high: assert property (@(posedge PCLK)
    (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b1);

rd_ena_low: assert property (@(posedge PCLK)
    !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> RD_ENA == 1'b0);

// WR_ENA and RD_ENA are mutually exclusive
wr_rd_ena_mutex: assert property (@(posedge PCLK)
    !(WR_ENA == 1'b1 && RD_ENA == 1'b1));

// PREADY correctness
pready_high: assert property (@(posedge PCLK)
    ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b1);

pready_low: assert property (@(posedge PCLK)
    !((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY == 1'b0);

// WRITE_DATA_ON_TX always equals PWDATA
write_data_on_tx_eq_pwdata: assert property (@(posedge PCLK)
    WRITE_DATA_ON_TX == PWDATA);

// PRDATA always equals READ_DATA_ON_RX
prdata_eq_read_data: assert property (@(posedge PCLK)
    PRDATA == READ_DATA_ON_RX);

// PSLVERR mirrors ERROR
pslverr_eq_error: assert property (@(posedge PCLK)
    PSLVERR == ERROR);

// INT_TX mirrors TX_EMPTY
int_tx_eq_tx_empty: assert property (@(posedge PCLK)
    INT_TX == TX_EMPTY);

// INT_RX mirrors RX_EMPTY
int_rx_eq_rx_empty: assert property (@(posedge PCLK)
    INT_RX == RX_EMPTY);

// Reset clears INTERNAL_I2C_REGISTER_CONFIG
reset_clears_config: assert property (@(posedge PCLK)
    !PRESETn |=> INTERNAL_I2C_REGISTER_CONFIG == 14'd0);

// Reset clears INTERNAL_I2C_REGISTER_TIMEOUT
reset_clears_timeout: assert property (@(posedge PCLK)
    !PRESETn |=> INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0);

// Config register updated correctly on PADDR=8
config_reg_update: assert property (@(posedge PCLK)
    (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
    INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]));

// Timeout register updated correctly on PADDR=12
timeout_reg_update: assert property (@(posedge PCLK)
    (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
    INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]));

// Config register holds value when not being written (not reset, not addr 8 write)
config_reg_holds: assert property (@(posedge PCLK)
    (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=>
    INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG));

// Timeout register holds when not reset and not addr 12 write
timeout_reg_holds: assert property (@(posedge PCLK)
    (PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)) |=>
    INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT));

// WR_ENA only asserted when PSELx is high
wr_ena_requires_pselx: assert property (@(posedge PCLK)
    WR_ENA == 1'b1 |-> PSELx == 1'b1);

// RD_ENA only asserted when PSELx is high
rd_ena_requires_pselx: assert property (@(posedge PCLK)
    RD_ENA == 1'b1 |-> PSELx == 1'b1);

// WR_ENA requires PENABLE
wr_ena_requires_penable: assert property (@(posedge PCLK)
    WR_ENA == 1'b1 |-> PENABLE == 1'b1);

// RD_ENA requires PENABLE
rd_ena_requires_penable: assert property (@(posedge PCLK)
    RD_ENA == 1'b1 |-> PENABLE == 1'b1);

// PREADY requires PENABLE and PSELx
pready_requires_penable_pselx: assert property (@(posedge PCLK)
    PREADY == 1'b1 |-> (PENABLE == 1'b1 && PSELx == 1'b1));

endmodule

bind apb apb_assert apb_assert_instance (.*);
