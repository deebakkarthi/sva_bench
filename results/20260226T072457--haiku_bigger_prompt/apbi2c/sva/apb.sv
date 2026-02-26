module apb_assert(
			//standard ARM
	    		input PCLK,
			input PRESETn,
			input PSELx,
			input PWRITE,
			input PENABLE,
			input [31:0] PADDR,
			input [31:0] PWDATA,

			//internal pin
			input [31:0] READ_DATA_ON_RX,
			input ERROR,
			input TX_EMPTY,
			input RX_EMPTY,
			
			//external pin
			output [31:0] PRDATA,

			//internal pin 
			output reg [13:0] INTERNAL_I2C_REGISTER_CONFIG,
			output reg [13:0] INTERNAL_I2C_REGISTER_TIMEOUT,
			output [31:0] WRITE_DATA_ON_TX,
			output  WR_ENA,
			output  RD_ENA,
			
			//outside port 
			output PREADY,
			output PSLVERR,

			//interruption
			output INT_RX,
			output INT_TX
	   
	  );

wr_ena_generation: assert property (WR_ENA iff (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx));

rd_ena_generation: assert property (RD_ENA iff (~PWRITE && PENABLE && (PADDR == 32'd4) && PSELx));

wr_rd_mutually_exclusive: assert property (~(WR_ENA && RD_ENA));

pready_generation: assert property (PREADY iff ((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx));

pslverr_passthrough: assert property (PSLVERR == ERROR);

int_tx_passthrough: assert property (INT_TX == TX_EMPTY);

int_rx_passthrough: assert property (INT_RX == RX_EMPTY);

write_data_passthrough: assert property (WRITE_DATA_ON_TX == PWDATA);

prdata_passthrough: assert property (PRDATA == READ_DATA_ON_RX);

config_register_on_reset: assert property (@(posedge PCLK) ~PRESETn |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == 14'd0));

timeout_register_on_reset: assert property (@(posedge PCLK) ~PRESETn |=> (apb.INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));

config_register_write_behavior: assert property (@(posedge PCLK) (PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

timeout_register_write_behavior: assert property (@(posedge PCLK) (PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> (apb.INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

config_register_hold_value: assert property (@(posedge PCLK) disable iff (~PRESETn) ~(PADDR == 32'd8 && PSELx && PWRITE && PREADY) |=> (apb.INTERNAL_I2C_REGISTER_CONFIG == $past(apb.INTERNAL_I2C_REGISTER_CONFIG)));

timeout_register_hold_value: assert property (@(posedge PCLK) disable iff (~PRESETn) ~(PADDR == 32'd12 && PSELx && PWRITE && PREADY) |=> (apb.INTERNAL_I2C_REGISTER_TIMEOUT == $past(apb.INTERNAL_I2C_REGISTER_TIMEOUT)));

endmodule

bind apb apb_assert apb_assert_instance (.*);
