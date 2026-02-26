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
    output WR_ENA,
    output RD_ENA,
    output PREADY,
    output PSLVERR,
    output INT_RX,
    output INT_TX
);

    // WR_ENA is asserted when PWRITE, PENABLE, PADDR==0, PSELx are all active
    wr_ena_high : assert property (@(posedge PCLK)
        (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx) |-> WR_ENA);

    wr_ena_low : assert property (@(posedge PCLK)
        !(PWRITE && PENABLE && (PADDR == 32'd0) && PSELx) |-> !WR_ENA);

    // RD_ENA is asserted when PWRITE is low, PENABLE, PADDR==4, PSELx are active
    rd_ena_high : assert property (@(posedge PCLK)
        (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx) |-> RD_ENA);

    rd_ena_low : assert property (@(posedge PCLK)
        !(!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx) |-> !RD_ENA);

    // PREADY is asserted when a valid transaction is in progress
    pready_high : assert property (@(posedge PCLK)
        ((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx) |-> PREADY);

    pready_low : assert property (@(posedge PCLK)
        !((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx) |-> !PREADY);

    // WRITE_DATA_ON_TX is always driven by PWDATA
    write_data_always_pwdata : assert property (@(posedge PCLK)
        WRITE_DATA_ON_TX == PWDATA);

    // PRDATA is always driven by READ_DATA_ON_RX
    prdata_always_read_data : assert property (@(posedge PCLK)
        PRDATA == READ_DATA_ON_RX);

    // PSLVERR directly reflects ERROR
    pslverr_reflects_error : assert property (@(posedge PCLK)
        PSLVERR == ERROR);

    // INT_TX directly reflects TX_EMPTY
    int_tx_reflects_tx_empty : assert property (@(posedge PCLK)
        INT_TX == TX_EMPTY);

    // INT_RX directly reflects RX_EMPTY
    int_rx_reflects_rx_empty : assert property (@(posedge PCLK)
        INT_RX == RX_EMPTY);

    // On reset, INTERNAL_I2C_REGISTER_CONFIG is cleared
    config_reg_reset : assert property (@(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0));

    // On reset, INTERNAL_I2C_REGISTER_TIMEOUT is cleared
    timeout_reg_reset : assert property (@(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));

    // Config register is updated with PWDATA[13:0] on a valid write to address 8
    config_reg_write : assert property (@(posedge PCLK)
        (PRESETn && (PADDR == 32'd8) && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

    // Timeout register is updated with PWDATA[13:0] on a valid write to address 12
    timeout_reg_write : assert property (@(posedge PCLK)
        (PRESETn && (PADDR == 32'd12) && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

    // Config register retains its value when not written to address 8
    config_reg_stable : assert property (@(posedge PCLK)
        (PRESETn && !((PADDR == 32'd8) && PSELx && PWRITE && PREADY)) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

    // Timeout register retains its value when not written to address 12
    timeout_reg_stable : assert property (@(posedge PCLK)
        (PRESETn && !((PADDR == 32'd12) && PSELx && PWRITE && PREADY)) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT)));

    // WR_ENA must not be active simultaneously with RD_ENA
    wr_rd_mutually_exclusive : assert property (@(posedge PCLK)
        !(WR_ENA && RD_ENA));

    // PREADY must not be asserted without PSELx active
    pready_requires_pselx : assert property (@(posedge PCLK)
        PREADY |-> PSELx);

    // PREADY must not be asserted without PENABLE active
    pready_requires_penable : assert property (@(posedge PCLK)
        PREADY |-> PENABLE);

endmodule

bind apb apb_assert apb_assert_instance (.*);
