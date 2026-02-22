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

    // WR_ENA assertion: active only when PWRITE=1, PENABLE=1, PADDR=0, PSELx=1
    wr_ena_high : assert property (
        @(posedge PCLK)
        (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b1)
    );

    wr_ena_low : assert property (
        @(posedge PCLK)
        !(PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1) |-> (WR_ENA == 1'b0)
    );

    // RD_ENA assertion: active only when PWRITE=0, PENABLE=1, PADDR=4, PSELx=1
    rd_ena_high : assert property (
        @(posedge PCLK)
        (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b1)
    );

    rd_ena_low : assert property (
        @(posedge PCLK)
        !(PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1) |-> (RD_ENA == 1'b0)
    );

    // PREADY assertion: active when (WR_ENA or RD_ENA or PADDR==8 or PADDR==12) and PENABLE and PSELx
    pready_high : assert property (
        @(posedge PCLK)
        ((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1)
        |-> (PREADY == 1'b1)
    );

    pready_low : assert property (
        @(posedge PCLK)
        !((WR_ENA == 1'b1 || RD_ENA == 1'b1 || PADDR == 32'd8 || PADDR == 32'd12) && PENABLE == 1'b1 && PSELx == 1'b1)
        |-> (PREADY == 1'b0)
    );

    // WRITE_DATA_ON_TX always equals PWDATA
    write_data_on_tx_equals_pwdata : assert property (
        @(posedge PCLK)
        (WRITE_DATA_ON_TX == PWDATA)
    );

    // PRDATA always equals READ_DATA_ON_RX
    prdata_equals_read_data_on_rx : assert property (
        @(posedge PCLK)
        (PRDATA == READ_DATA_ON_RX)
    );

    // PSLVERR equals ERROR
    pslverr_equals_error : assert property (
        @(posedge PCLK)
        (PSLVERR == ERROR)
    );

    // INT_TX equals TX_EMPTY
    int_tx_equals_tx_empty : assert property (
        @(posedge PCLK)
        (INT_TX == TX_EMPTY)
    );

    // INT_RX equals RX_EMPTY
    int_rx_equals_rx_empty : assert property (
        @(posedge PCLK)
        (INT_RX == RX_EMPTY)
    );

    // On reset, INTERNAL_I2C_REGISTER_CONFIG should be 0
    reset_config_register : assert property (
        @(posedge PCLK)
        (!PRESETn) |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    // On reset, INTERNAL_I2C_REGISTER_TIMEOUT should be 0
    reset_timeout_register : assert property (
        @(posedge PCLK)
        (!PRESETn) |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // INTERNAL_I2C_REGISTER_CONFIG updated with PWDATA[13:0] when PADDR==8, PSELx=1, PWRITE=1, PREADY=1
    config_register_write : assert property (
        @(posedge PCLK)
        (PRESETn && PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    // INTERNAL_I2C_REGISTER_TIMEOUT updated with PWDATA[13:0] when PADDR==12, PSELx=1, PWRITE=1, PREADY=1
    timeout_register_write : assert property (
        @(posedge PCLK)
        (PRESETn && PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1)
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // INTERNAL_I2C_REGISTER_CONFIG holds its value when not being written and not in reset
    config_register_hold : assert property (
        @(posedge PCLK)
        (PRESETn && !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
        |=> (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    // INTERNAL_I2C_REGISTER_TIMEOUT holds its value when not being written and not in reset
    timeout_register_hold : assert property (
        @(posedge PCLK)
        (PRESETn && !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1))
        |=> (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // WR_ENA and RD_ENA should never be simultaneously active
    wr_rd_ena_mutually_exclusive : assert property (
        @(posedge PCLK)
        !(WR_ENA == 1'b1 && RD_ENA == 1'b1)
    );

    // PREADY should not be active without PENABLE and PSELx
    pready_requires_penable_pselx : assert property (
        @(posedge PCLK)
        (PREADY == 1'b1) |-> (PENABLE == 1'b1 && PSELx == 1'b1)
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
