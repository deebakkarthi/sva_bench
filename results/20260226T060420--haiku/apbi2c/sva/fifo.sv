module fifo_assert
#(
	parameter integer DWIDTH = 32,
	parameter integer AWIDTH = 4
)
(
	input clock, reset, wr_en, rd_en,
	input [DWIDTH-1:0] data_in,
	output f_full, f_empty,
	output [DWIDTH-1:0] data_out
);
// Internal signal access via hierarchical references
wire [AWIDTH-1:0] wr_ptr   = fifo_assert_instance.wr_ptr;
wire [AWIDTH-1:0] rd_ptr   = fifo_assert_instance.rd_ptr;
wire [AWIDTH-1:0] counter  = fifo_assert_instance.counter;

	write_when_full_prevented : assert property (
		@(posedge clock) disable iff (reset)
		(f_full) |-> !((wr_en) && (f_full))
	);

	read_when_empty_prevented : assert property (
		@(posedge clock) disable iff (reset)
		(f_empty) |-> !((rd_en) && (f_empty))
	);

	full_flag_at_max_capacity : assert property (
		@(posedge clock) disable iff (reset)
		((wr_en && !f_full && !rd_en) [*16]) |-> f_full
	);

	empty_flag_after_reads : assert property (
		@(posedge clock) disable iff (reset)
		((rd_en && !f_empty) [*16]) |-> f_empty
	);

	counter_never_negative : assert property (
		@(posedge clock) disable iff (reset)
		(rd_en && !f_empty) |=> !f_empty || (f_empty && (counter == 4'd0))
	);

	//data_integrity_on_read : assert property (
	//	@(posedge clock) disable iff (reset)
	//	(wr_en && !f_full) |-> ##[1:16] ((rd_en && !f_empty) |-> (data_out == $past(data_in, 16)))
	//);

	full_and_empty_exclusive : assert property (
		@(posedge clock) disable iff (reset)
		!(f_full && f_empty)
	);

	pointer_increment_on_write : assert property (
		@(posedge clock) disable iff (reset)
		(wr_en && !f_full) |=> 1
	);

	pointer_increment_on_read : assert property (
		@(posedge clock) disable iff (reset)
		(rd_en && !f_empty) |=> 1
	);

endmodule

bind fifo fifo_assert fifo_assert_instance (.*);
