module fifo_assert #(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock,
	input reset,
	input wr_en,
	input rd_en,
	input [DWIDTH-1:0] data_in,
	input f_full,
	input f_empty,
	input [DWIDTH-1:0] data_out
);

// f_full is asserted when counter equals 15
full_when_counter_max: assert property (@(posedge clock) (fifo.counter == 4'd15) |-> f_full == 1'b1);

// f_full is deasserted when counter is not 15
not_full_when_counter_not_max: assert property (@(posedge clock) (fifo.counter != 4'd15) |-> f_full == 1'b0);

// f_empty is asserted when counter equals 0
empty_when_counter_zero: assert property (@(posedge clock) (fifo.counter == 4'd0) |-> f_empty == 1'b1);

// f_empty is deasserted when counter is not 0
not_empty_when_counter_not_zero: assert property (@(posedge clock) (fifo.counter != 4'd0) |-> f_empty == 1'b0);

// FIFO cannot be both full and empty simultaneously
not_full_and_empty: assert property (@(posedge clock) f_full |-> !f_empty);

// After reset, write pointer is zero
reset_wr_ptr_zero: assert property (@(posedge clock) reset |=> fifo.wr_ptr == {(AWIDTH){1'b0}});

// After reset, read pointer is zero
reset_rd_ptr_zero: assert property (@(posedge clock) reset |=> fifo.rd_ptr == {(AWIDTH){1'b0}});

// After reset, counter is zero
reset_counter_zero: assert property (@(posedge clock) reset |=> fifo.counter == {(AWIDTH){1'b0}});

// After reset, FIFO is empty
reset_fifo_empty: assert property (@(posedge clock) reset |=> f_empty == 1'b1);

// After reset, FIFO is not full
reset_fifo_not_full: assert property (@(posedge clock) reset |=> f_full == 1'b0);

// Write when full is ignored: write pointer does not change when full
no_write_when_full: assert property (@(posedge clock) (!reset && wr_en && f_full) |=> fifo.wr_ptr == $past(fifo.wr_ptr));

// Read when empty is ignored: read pointer does not change when empty
no_read_when_empty: assert property (@(posedge clock) (!reset && rd_en && f_empty) |=> fifo.rd_ptr == $past(fifo.rd_ptr));

// Write pointer increments on valid write
wr_ptr_increment_on_write: assert property (@(posedge clock) (!reset && wr_en && !f_full) |=> fifo.wr_ptr == $past(fifo.wr_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1});

// Read pointer increments on valid read
rd_ptr_increment_on_read: assert property (@(posedge clock) (!reset && rd_en && !f_empty) |=> fifo.rd_ptr == $past(fifo.rd_ptr) + {{(AWIDTH-1){1'b0}}, 1'b1});

// Counter increments on valid write only (no simultaneous read)
counter_inc_on_write_only: assert property (@(posedge clock) (!reset && wr_en && !f_full && !rd_en) |=> fifo.counter == $past(fifo.counter) + {{(AWIDTH-1){1'b0}}, 1'b1});

// Counter decrements on valid read only (no simultaneous write)
counter_dec_on_read_only: assert property (@(posedge clock) (!reset && rd_en && !f_empty && !wr_en) |=> fifo.counter == $past(fifo.counter) - {{(AWIDTH-1){1'b0}}, 1'b1});

// Counter unchanged on simultaneous read and write when not full and not empty
counter_stable_on_simultaneous_rw: assert property (@(posedge clock) (!reset && wr_en && rd_en && !f_full && !f_empty) |=> fifo.counter == $past(fifo.counter));

// Counter unchanged when no read and no write
counter_stable_no_rw: assert property (@(posedge clock) (!reset && !wr_en && !rd_en) |=> fifo.counter == $past(fifo.counter));

// data_out always reflects memory at read pointer
data_out_from_mem: assert property (@(posedge clock) 1'b1 |-> data_out == fifo.mem[fifo.rd_ptr]);

// Counter is bounded
counter_bounded: assert property (@(posedge clock) fifo.counter <= 4'd15);

// Write pointer stable when no valid write
wr_ptr_stable_no_write: assert property (@(posedge clock) (!reset && !(wr_en && !f_full)) |=> fifo.wr_ptr == $past(fifo.wr_ptr));

// Read pointer stable when no valid read
rd_ptr_stable_no_read: assert property (@(posedge clock) (!reset && !(rd_en && !f_empty)) |=> fifo.rd_ptr == $past(fifo.rd_ptr));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
