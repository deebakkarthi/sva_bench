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

    // ------------------------------------------------------------------
    // Combinational output correctness
    // ------------------------------------------------------------------

    wr_ena_iff_pwrite_penable_pselx_addr0 : assert property (
        @(posedge PCLK)
        WR_ENA == (PWRITE == 1'b1 && PENABLE == 1'b1 && PADDR == 32'd0 && PSELx == 1'b1)
    );

    rd_ena_iff_no_pwrite_penable_pselx_addr4 : assert property (
        @(posedge PCLK)
        RD_ENA == (PWRITE == 1'b0 && PENABLE == 1'b1 && PADDR == 32'd4 && PSELx == 1'b1)
    );

    pready_iff_correct_condition : assert property (
        @(posedge PCLK)
        PREADY == ((WR_ENA || RD_ENA || PADDR == 32'd8 || PADDR == 32'd12) &&
                   (PENABLE == 1'b1 && PSELx == 1'b1))
    );

    write_data_on_tx_equals_pwdata : assert property (
        @(posedge PCLK) WRITE_DATA_ON_TX == PWDATA
    );

    prdata_equals_read_data_on_rx : assert property (
        @(posedge PCLK) PRDATA == READ_DATA_ON_RX
    );

    pslverr_equals_error : assert property (
        @(posedge PCLK) PSLVERR == ERROR
    );

    int_tx_equals_tx_empty : assert property (
        @(posedge PCLK) INT_TX == TX_EMPTY
    );

    int_rx_equals_rx_empty : assert property (
        @(posedge PCLK) INT_RX == RX_EMPTY
    );

    // ------------------------------------------------------------------
    // WR_ENA / RD_ENA implications
    // ------------------------------------------------------------------

    wr_ena_requires_pwrite_high : assert property (
        @(posedge PCLK) WR_ENA |-> PWRITE
    );

    wr_ena_requires_penable : assert property (
        @(posedge PCLK) WR_ENA |-> PENABLE
    );

    wr_ena_requires_pselx : assert property (
        @(posedge PCLK) WR_ENA |-> PSELx
    );

    wr_ena_requires_paddr_zero : assert property (
        @(posedge PCLK) WR_ENA |-> (PADDR == 32'd0)
    );

    rd_ena_requires_pwrite_low : assert property (
        @(posedge PCLK) RD_ENA |-> !PWRITE
    );

    rd_ena_requires_penable : assert property (
        @(posedge PCLK) RD_ENA |-> PENABLE
    );

    rd_ena_requires_pselx : assert property (
        @(posedge PCLK) RD_ENA |-> PSELx
    );

    rd_ena_requires_paddr_four : assert property (
        @(posedge PCLK) RD_ENA |-> (PADDR == 32'd4)
    );

    wr_ena_and_rd_ena_mutually_exclusive : assert property (
        @(posedge PCLK) !(WR_ENA && RD_ENA)
    );

    // ------------------------------------------------------------------
    // PREADY implications
    // ------------------------------------------------------------------

    pready_requires_penable : assert property (
        @(posedge PCLK) PREADY |-> PENABLE
    );

    pready_requires_pselx : assert property (
        @(posedge PCLK) PREADY |-> PSELx
    );

    pready_deasserted_when_penable_low : assert property (
        @(posedge PCLK) !PENABLE |-> !PREADY
    );

    pready_deasserted_when_pselx_low : assert property (
        @(posedge PCLK) !PSELx |-> !PREADY
    );

    wr_ena_implies_pready : assert property (
        @(posedge PCLK) WR_ENA |-> PREADY
    );

    rd_ena_implies_pready : assert property (
        @(posedge PCLK) RD_ENA |-> PREADY
    );

    pready_asserted_when_addr8_penable_pselx : assert property (
        @(posedge PCLK) (PADDR == 32'd8 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY
    );

    pready_asserted_when_addr12_penable_pselx : assert property (
        @(posedge PCLK) (PADDR == 32'd12 && PENABLE == 1'b1 && PSELx == 1'b1) |-> PREADY
    );

    pready_not_asserted_without_valid_addr : assert property (
        @(posedge PCLK)
        (PENABLE && PSELx &&
         PADDR != 32'd0 && PADDR != 32'd4 &&
         PADDR != 32'd8 && PADDR != 32'd12) |-> !PREADY
    );

    // ------------------------------------------------------------------
    // WR_ENA / RD_ENA deasserted when PENABLE or PSELx low
    // ------------------------------------------------------------------

    wr_ena_deasserted_when_penable_low : assert property (
        @(posedge PCLK) !PENABLE |-> !WR_ENA
    );

    wr_ena_deasserted_when_pselx_low : assert property (
        @(posedge PCLK) !PSELx |-> !WR_ENA
    );

    rd_ena_deasserted_when_penable_low : assert property (
        @(posedge PCLK) !PENABLE |-> !RD_ENA
    );

    rd_ena_deasserted_when_pselx_low : assert property (
        @(posedge PCLK) !PSELx |-> !RD_ENA
    );

    // ------------------------------------------------------------------
    // Sequential: reset behaviour
    // ------------------------------------------------------------------

    config_reg_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_CONFIG == 14'd0)
    );

    timeout_reg_resets_to_zero : assert property (
        @(posedge PCLK) !PRESETn |=> (INTERNAL_I2C_REGISTER_TIMEOUT == 14'd0)
    );

    // ------------------------------------------------------------------
    // Sequential: register captures on write
    // ------------------------------------------------------------------

    config_reg_captures_pwdata_on_addr8_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(PWDATA[13:0]))
    );

    timeout_reg_captures_pwdata_on_addr12_write : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(PWDATA[13:0]))
    );

    // ------------------------------------------------------------------
    // Sequential: registers hold value when not written
    // ------------------------------------------------------------------

    config_reg_stable_when_not_written_to_addr8 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_CONFIG == $past(INTERNAL_I2C_REGISTER_CONFIG))
    );

    timeout_reg_stable_when_not_written_to_addr12 : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        !(PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1 && PREADY == 1'b1) |=>
        (INTERNAL_I2C_REGISTER_TIMEOUT == $past(INTERNAL_I2C_REGISTER_TIMEOUT))
    );

    // ------------------------------------------------------------------
    // Config write to addr 8 requires PREADY (which in turn needs PENABLE & PSELx)
    // ------------------------------------------------------------------

    config_write_only_when_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd8 && PSELx == 1'b1 && PWRITE == 1'b1) |->
        (PREADY == PENABLE)
    );

    timeout_write_only_when_pready : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        (PADDR == 32'd12 && PSELx == 1'b1 && PWRITE == 1'b1) |->
        (PREADY == PENABLE)
    );

    // ------------------------------------------------------------------
    // Known-value checks for outputs during normal operation
    // ------------------------------------------------------------------

    pslverr_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR !== 1'bx
    );

    pready_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        PREADY !== 1'bx
    );

    wr_ena_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        WR_ENA !== 1'bx
    );

    rd_ena_known_after_reset : assert property (
        @(posedge PCLK) disable iff (!PRESETn)
        RD_ENA !== 1'bx
    );

endmodule

bind apb apb_assert apb_assert_instance (.*);
