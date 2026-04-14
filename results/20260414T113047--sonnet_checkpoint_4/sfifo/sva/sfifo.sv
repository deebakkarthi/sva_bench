module sfifo_assert #(
		parameter	DW=8,
		parameter	LGFLEN=4
	) (
		input	wire		i_clk, i_reset,
		input	wire		i_wr,
		input	wire [(DW-1):0]	i_data,
		input	reg		o_full,
		input	wire		i_rd,
		input	wire [(DW-1):0]	o_data,
		input	reg		o_empty,
		input	wire		o_err
	);

	// After reset: o_empty must be high
	reset_empty: assert property (@(posedge i_clk) i_reset |=> o_empty);

	// After reset: o_full must be low
	reset_not_full: assert property (@(posedge i_clk) i_reset |=> !o_full);

	// After reset: write address must be zero
	reset_wraddr: assert property (@(posedge i_clk) i_reset |=> sfifo.wraddr == 0);

	// After reset: read address must be zero
	reset_rdaddr: assert property (@(posedge i_clk) i_reset |=> sfifo.rdaddr == 0);

	// After reset: overflow flag must be cleared
	reset_ovfl: assert property (@(posedge i_clk) i_reset |=> !sfifo.r_ovfl);

	// After reset: underflow flag must be cleared
	reset_unfl: assert property (@(posedge i_clk) i_reset |=> !sfifo.r_unfl);

	// o_full and o_empty must never both be true simultaneously
	not_full_and_empty: assert property (@(posedge i_clk) !(o_full && o_empty));

	// o_full must match the address pointer full condition
	full_iff_addr: assert property (@(posedge i_clk)
		!i_reset |->
		(o_full == ((sfifo.wraddr[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0])
		            && (sfifo.wraddr[LGFLEN] != sfifo.rdaddr[LGFLEN]))));

	// o_empty must match the address pointer empty condition
	empty_iff_addr: assert property (@(posedge i_clk)
		!i_reset |->
		(o_empty == (sfifo.wraddr == sfifo.rdaddr)));

	// Write pointer increments on a valid write (not full, or simultaneous read)
	wraddr_increments_on_write: assert property (@(posedge i_clk)
		(!i_reset && i_wr && (!o_full || i_rd)) |=>
		sfifo.wraddr == $past(sfifo.wraddr) + 1);

	// Write pointer must not advance when FIFO is full and no read (overflow)
	wraddr_stable_on_overflow: assert property (@(posedge i_clk)
		(!i_reset && i_wr && o_full && !i_rd) |=>
		sfifo.wraddr == $past(sfifo.wraddr));

	// Write pointer must remain stable when not writing
	wraddr_stable_no_write: assert property (@(posedge i_clk)
		(!i_reset && !i_wr) |=>
		sfifo.wraddr == $past(sfifo.wraddr));

	// Read pointer increments on a valid read (not empty)
	rdaddr_increments_on_read: assert property (@(posedge i_clk)
		(!i_reset && i_rd && !o_empty) |=>
		sfifo.rdaddr == $past(sfifo.rdaddr) + 1);

	// Read pointer must not advance when FIFO is empty (underflow)
	rdaddr_stable_on_underflow: assert property (@(posedge i_clk)
		(!i_reset && i_rd && o_empty) |=>
		sfifo.rdaddr == $past(sfifo.rdaddr));

	// Read pointer must remain stable when not reading
	rdaddr_stable_no_read: assert property (@(posedge i_clk)
		(!i_reset && !i_rd) |=>
		sfifo.rdaddr == $past(sfifo.rdaddr));

	// Overflow flag must be set after a write to a full FIFO with no simultaneous read
	overflow_sets_flag: assert property (@(posedge i_clk)
		(!i_reset && i_wr && o_full && !i_rd) |=> sfifo.r_ovfl);

	// Underflow flag must be set after a read from an empty FIFO
	underflow_sets_flag: assert property (@(posedge i_clk)
		(!i_reset && i_rd && o_empty) |=> sfifo.r_unfl);

	// Overflow flag must be sticky (stays set until reset)
	ovfl_sticky: assert property (@(posedge i_clk)
		(!i_reset && sfifo.r_ovfl) |=> sfifo.r_ovfl);

	// Underflow flag must be sticky (stays set until reset)
	unfl_sticky: assert property (@(posedge i_clk)
		(!i_reset && sfifo.r_unfl) |=> sfifo.r_unfl);

	// o_err must equal the OR of the overflow and underflow flags
	err_reflects_flags: assert property (@(posedge i_clk)
		o_err == (sfifo.r_ovfl || sfifo.r_unfl));

	// A read without write must clear o_full on the next cycle
	full_clears_on_read_only: assert property (@(posedge i_clk)
		(!i_reset && o_full && i_rd && !i_wr) |=> !o_full);

	// A write without read must clear o_empty on the next cycle
	empty_clears_on_write_only: assert property (@(posedge i_clk)
		(!i_reset && o_empty && i_wr) |=> !o_empty);

	// A read that drains the last entry must set o_empty (no simultaneous write)
	last_read_sets_empty: assert property (@(posedge i_clk)
		(!i_reset && !o_empty && i_rd && !i_wr
		 && (sfifo.w_rdaddr_plus_one == sfifo.wraddr)) |=> o_empty);

	// A write that fills the FIFO must set o_full (no simultaneous read)
	last_write_sets_full: assert property (@(posedge i_clk)
		(!i_reset && !o_full && i_wr && !i_rd
		 && (sfifo.w_wraddr_plus_one[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0])
		 && (sfifo.w_wraddr_plus_one[LGFLEN] != sfifo.rdaddr[LGFLEN])) |=> o_full);

	// Simultaneous full read-write must keep o_full high
	simultaneous_rw_keeps_full: assert property (@(posedge i_clk)
		(!i_reset && o_full && i_wr && i_rd) |=> o_full);

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
