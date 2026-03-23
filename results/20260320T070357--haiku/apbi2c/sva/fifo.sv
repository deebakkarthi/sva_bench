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

	full_flag_when_counter_max: assert property (@(posedge clock) (fifo.counter == 4'd15) |-> f_full);
	not_full_flag_when_counter_below_max: assert property (@(posedge clock) (fifo.counter != 4'd15) |-> !f_full);
	
	empty_flag_when_counter_zero: assert property (@(posedge clock) (fifo.counter == 4'd0) |-> f_empty);
	not_empty_flag_when_counter_nonzero: assert property (@(posedge clock) (fifo.counter != 4'd0) |-> !f_empty);
	
	write_pointer_resets_on_reset: assert property (@(posedge clock) reset |=> (fifo.wr_ptr == {(AWIDTH){1'b0}}));
	
	read_pointer_resets_on_reset: assert property (@(posedge clock) reset |=> (fifo.rd_ptr == {(AWIDTH){1'b0}}));
	
	counter_resets_on_reset: assert property (@(posedge clock) reset |=> (fifo.counter == {(AWIDTH){1'b0}}));
	
	write_pointer_increments_when_write_enabled: assert property (@(posedge clock) (wr_en && !f_full) |=> (fifo.wr_ptr == fifo.wr + 4'd1));
	
	read_pointer_increments_when_read_enabled: assert property (@(posedge clock) (rd_en && !f_empty) |=> (fifo.rd_ptr == fifo.rd + 4'd1));

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
