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

    // WR_ENA is asserted iff PWRITE, PENABLE, PSELx, and PADDR==0 are all active
    wr_ena_condition : assert property (@(posedge PCLK)
        WR_ENA == (PWRITE && PENABLE && (PADDR == 32'd0) && PSELx));

    // RD_ENA is asserted iff not PWRITE, PENABLE, PSELx, and PADDR==4 are active
    rd_ena_condition : assert property (@(posedge PCLK)
        RD_ENA == (!PWRITE && PENABLE && (PADDR == 32'd4) && PSELx));

    // PREADY is asserted for any valid selected+enabled transfer to known addresses
    pready_valid_transfer : assert property (@(posedge PCLK)
        PREADY == ((WR_ENA || RD_ENA || (PADDR == 32'd8) || (PADDR == 32'd12)) && PENABLE && PSELx));

    // WRITE_DATA_ON_TX is always a direct passthrough of PWDATA
    write_data_passthrough_to_tx : assert property (@(posedge PCLK)
        WRITE_DATA_ON_TX == PWDATA);

    // PRDATA is always a direct passthrough of READ_DATA_ON_RX
    rx_data_forwarded_to_prdata : assert property (@(posedge PCLK)
        PRDATA == READ_DATA_ON_RX);

    // PSLVERR reflects the ERROR input directly
    pslverr_mirrors_error_input : assert property (@(posedge PCLK)
        PSLVERR == ERROR);

    // INT_TX reflects the TX_EMPTY interrupt input
    int_tx_mirrors_tx_empty : assert property (@(posedge PCLK)
        INT_TX == TX_EMPTY);

    // INT_RX reflects the RX_EMPTY interrupt input
    int_rx_mirrors_rx_empty : assert property (@(posedge PCLK)
        INT_RX == RX_EMPTY);

    // After reset, INTERNAL_I2C_REGISTER_CONFIG must be cleared to 0
    config_reg_cleared_on_reset : assert property (@(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0));

    // After reset, INTERNAL_I2C_REGISTER_TIMEOUT must be cleared to 0
    timeout_reg_cleared_on_reset : assert property (@(posedge PCLK)
        !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0));

    // Writing to address 8 with PSELx, PWRITE, PREADY captures PWDATA[13:0] into config register
    config_reg_written_at_addr8 : assert property (@(posedge PCLK)
        (PRESETn && (PADDR == 32'd8) && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0])));

    // Writing to address 12 with PSELx, PWRITE, PREADY captures PWDATA[13:0] into timeout register
    timeout_reg_written_at_addr12 : assert property (@(posedge PCLK)
        (PRESETn && (PADDR == 32'd12) && PSELx && PWRITE && PREADY) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0])));

    // PREADY can only be high when PENABLE and PSELx are both asserted
    pready_requires_penable_and_pselx : assert property (@(posedge PCLK)
        PREADY |-> (PENABLE && PSELx));

    // WR_ENA requires PWRITE to be set
    wr_ena_requires_pwrite : assert property (@(posedge PCLK)
        WR_ENA |-> PWRITE);

    // RD_ENA requires PWRITE to be clear
    rd_ena_requires_read_direction : assert property (@(posedge PCLK)
        RD_ENA |-> !PWRITE);

    // WR_ENA and RD_ENA are mutually exclusive
    wr_rd_ena_mutually_exclusive : assert property (@(posedge PCLK)
        !(WR_ENA && RD_ENA));

    // WR_ENA requires PENABLE
    wr_ena_requires_penable : assert property (@(posedge PCLK)
        WR_ENA |-> PENABLE);

    // RD_ENA requires PENABLE
    rd_ena_requires_penable : assert property (@(posedge PCLK)
        RD_ENA |-> PENABLE);

    // WR_ENA can only target PADDR 0
    wr_ena_only_at_addr0 : assert property (@(posedge PCLK)
        WR_ENA |-> (PADDR == 32'd0));

    // RD_ENA can only target PADDR 4
    rd_ena_only_at_addr4 : assert property (@(posedge PCLK)
        RD_ENA |-> (PADDR == 32'd4));

    // Config register holds value when not being written
    config_reg_stable_when_not_written : assert property (@(posedge PCLK)
        (PRESETn && !(!PRESETn) && !(PADDR == 32'd8 && PSELx && PWRITE && PREADY)) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG)));

endmodule

bind apb apb_assert apb_assert_instance (.*);
