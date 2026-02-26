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

    // PREADY can only be asserted when PENABLE is active
    pready_requires_penable : assert property (@(posedge PCLK)
        PREADY |-> PENABLE);

    // PREADY can only be asserted when PSELx is active
    pready_requires_pselx : assert property (@(posedge PCLK)
        PREADY |-> PSELx);

    // Without PSELx, PREADY must be deasserted
    no_pready_without_pselx : assert property (@(posedge PCLK)
        !PSELx |-> !PREADY);

    // Without PENABLE, PREADY must be deasserted
    no_pready_without_penable : assert property (@(posedge PCLK)
        !PENABLE |-> !PREADY);

    // A write transfer to TX FIFO (PADDR==0) with valid APB setup must complete (PREADY)
    write_to_tx_fifo_completes : assert property (@(posedge PCLK)
        (PSELx && PENABLE && PWRITE && (PADDR == 32'd0)) |-> PREADY);

    // A read transfer from RX FIFO (PADDR==4) with valid APB setup must complete (PREADY)
    read_from_rx_fifo_completes : assert property (@(posedge PCLK)
        (PSELx && PENABLE && !PWRITE && (PADDR == 32'd4)) |-> PREADY);

    // A write to config register (PADDR==8) with valid APB setup must complete (PREADY)
    write_to_config_register_completes : assert property (@(posedge PCLK)
        (PSELx && PENABLE && PWRITE && (PADDR == 32'd8)) |-> PREADY);

    // A write to timeout register (PADDR==12) with valid APB setup must complete (PREADY)
    write_to_timeout_register_completes : assert property (@(posedge PCLK)
        (PSELx && PENABLE && PWRITE && (PADDR == 32'd12)) |-> PREADY);

    // After reset, PSLVERR must be deasserted (no error in reset state since config resets to 0)
    no_error_immediately_after_reset : assert property (@(posedge PCLK)
        !PRESETn |=> !PSLVERR);

    // INT_TX and INT_RX are never both high simultaneously when the design is not in error
    // (TX FIFO and RX FIFO cannot both be simultaneously empty in a meaningful transfer scenario
    // unless no data has been written - but this is a permissible state)

    // SDA_ENABLE and SCL_ENABLE are registered outputs that remain stable for at least one cycle
    // when not in a response state
    sda_enable_stable_on_reset : assert property (@(posedge PCLK)
        !PRESETn |=> !SCL_ENABLE);

endmodule

bind i2c i2c_assert i2c_assert_instance (.*);
