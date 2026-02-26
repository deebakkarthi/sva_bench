module fifo_assert #(
    parameter integer DWIDTH = 32,
    parameter integer AWIDTH = 4
)(
    input clock,
    input reset,
    input wr_en,
    input rd_en,
    input [DWIDTH-1:0] data_in,
    output f_full,
    output f_empty,
    output [DWIDTH-1:0] data_out
);

    // f_full and f_empty are mutually exclusive
    full_and_empty_mutually_exclusive : assert property (@(posedge clock)
        !(f_full && f_empty));

    // After reset, FIFO must report empty
    reset_forces_empty : assert property (@(posedge clock)
        reset |=> f_empty);

    // After reset, FIFO must not be full
    reset_forces_not_full : assert property (@(posedge clock)
        reset |=> !f_full);

    // A full FIFO with write-only stays full
    full_stays_full_on_write_only : assert property (@(posedge clock)
        (f_full && wr_en && !rd_en) |=> f_full);

    // An empty FIFO with read-only stays empty
    empty_stays_empty_on_read_only : assert property (@(posedge clock)
        (f_empty && rd_en && !wr_en) |=> f_empty);

    // Writing to a non-full FIFO (no concurrent read) makes it non-empty
    write_only_makes_nonempty : assert property (@(posedge clock)
        (!reset && wr_en && !rd_en && !f_full) |=> !f_empty);

    // Reading from a non-empty FIFO (no concurrent write) makes it non-full
    read_only_makes_nonfull : assert property (@(posedge clock)
        (!reset && rd_en && !wr_en && !f_empty) |=> !f_full);

    // Simultaneous read and write on a non-boundary FIFO preserves fill status
    simultaneous_rw_preserves_fill : assert property (@(posedge clock)
        (!reset && wr_en && rd_en && !f_full && !f_empty) |=>
        (f_full == $past(f_full) && f_empty == $past(f_empty)));

    // A full FIFO with no read must remain full on the next cycle
    full_persists_without_read : assert property (@(posedge clock)
        (!reset && f_full && !rd_en) |=> f_full);

    // An empty FIFO with no write must remain empty on the next cycle
    empty_persists_without_write : assert property (@(posedge clock)
        (!reset && f_empty && !wr_en) |=> f_empty);

    // After writing to a full FIFO simultaneously with a read, it is still not empty
    full_rw_stays_nonempty : assert property (@(posedge clock)
        (!reset && f_full && wr_en && rd_en) |=> !f_empty);

    // After reading from an empty FIFO simultaneously with a write, it is still not full
    empty_rw_stays_nonfull : assert property (@(posedge clock)
        (!reset && f_empty && wr_en && rd_en) |=> !f_full);

endmodule

bind fifo fifo_assert #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH)) fifo_assert_instance (.*);
