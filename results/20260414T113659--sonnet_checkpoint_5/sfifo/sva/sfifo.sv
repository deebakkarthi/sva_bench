module sfifo_assert #(
		parameter DW=8,
		parameter LGFLEN=4
	) (
		input wire i_clk, i_reset,
		input wire i_wr,
		input wire [(DW-1):0] i_data,
		input wire o_full,
		input wire i_rd,
		input wire [(DW-1):0] o_data,
		input wire o_empty,
		input wire o_err
	);

	localparam FLEN = (1<<LGFLEN);

	// Reset behaviour
	reset_clears_full:       assert property (@(posedge i_clk) i_reset |=> !o_full);
	reset_sets_empty:        assert property (@(posedge i_clk) i_reset |=> o_empty);
	reset_clears_wraddr:     assert property (@(posedge i_clk) i_reset |=> (sfifo.wraddr == 0));
	reset_clears_rdaddr:     assert property (@(posedge i_clk) i_reset |=> (sfifo.rdaddr == 0));
	reset_clears_ovfl:       assert property (@(posedge i_clk) i_reset |=> !sfifo.r_ovfl);
	reset_clears_unfl:       assert property (@(posedge i_clk) i_reset |=> !sfifo.r_unfl);

	// Mutual exclusion
	full_and_empty_mutex:    assert property (@(posedge i_clk) !(o_full && o_empty));

	// Address pointer relationships
	wraddr_increments_on_wr: assert property (@(posedge i_clk) disable iff (i_reset)
		sfifo.w_wr |=> (sfifo.wraddr == $past(sfifo.wraddr) + 1'b1));

	wraddr_stable_when_no_wr: assert property (@(posedge i_clk) disable iff (i_reset)
		!sfifo.w_wr |=> (sfifo.wraddr == $past(sfifo.wraddr)));

	rdaddr_increments_on_rd: assert property (@(posedge i_clk) disable iff (i_reset)
		sfifo.w_rd |=> (sfifo.rdaddr == $past(sfifo.rdaddr) + 1'b1));

	rdaddr_stable_when_no_rd: assert property (@(posedge i_clk) disable iff (i_reset)
		!sfifo.w_rd |=> (sfifo.rdaddr == $past(sfifo.rdaddr)));

	// Fill level stays in valid range [0, FLEN]
	fill_level_in_range:     assert property (@(posedge i_clk)
		((sfifo.wraddr - sfifo.rdaddr) <= FLEN[LGFLEN:0]));

	// o_empty consistency with pointers
	empty_iff_ptrs_equal:    assert property (@(posedge i_clk)
		o_empty == (sfifo.wraddr == sfifo.rdaddr));

	// o_full consistency with pointers (same lower bits, different MSB)
	full_iff_ptrs_wrapped:   assert property (@(posedge i_clk)
		o_full == ((sfifo.wraddr[LGFLEN-1:0] == sfifo.rdaddr[LGFLEN-1:0])
		           && (sfifo.wraddr[LGFLEN] != sfifo.rdaddr[LGFLEN])));

	// w_wr and w_rd definitions
	w_wr_definition:         assert property (@(posedge i_clk)
		sfifo.w_wr == (i_wr && (!o_full || i_rd)));

	w_rd_definition:         assert property (@(posedge i_clk)
		sfifo.w_rd == (i_rd && !o_empty));

	// Overflow: write to full FIFO without simultaneous read sets r_ovfl
	ovfl_set_on_full_write:  assert property (@(posedge i_clk) disable iff (i_reset)
		(o_full && i_wr && !i_rd) |=> sfifo.r_ovfl);

	// wraddr must not advance on overflow attempt
	wraddr_frozen_on_overflow: assert property (@(posedge i_clk) disable iff (i_reset)
		(o_full && i_wr && !i_rd) |=> (sfifo.wraddr == $past(sfifo.wraddr)));

	// Underflow: read from empty FIFO sets r_unfl
	unfl_set_on_empty_read:  assert property (@(posedge i_clk) disable iff (i_reset)
		(o_empty && i_rd) |=> sfifo.r_unfl);

	// rdaddr must not advance on underflow attempt
	rdaddr_frozen_on_underflow: assert property (@(posedge i_clk) disable iff (i_reset)
		(o_empty && i_rd) |=> (sfifo.rdaddr == $past(sfifo.rdaddr)));

	// Error flags are sticky once set
	ovfl_flag_sticky:        assert property (@(posedge i_clk) disable iff (i_reset)
		sfifo.r_ovfl |=> sfifo.r_ovfl);

	unfl_flag_sticky:        assert property (@(posedge i_clk) disable iff (i_reset)
		sfifo.r_unfl |=> sfifo.r_unfl);

	// o_err is OR of both error flags
	err_is_ovfl_or_unfl:     assert property (@(posedge i_clk)
		o_err == (sfifo.r_ovfl || sfifo.r_unfl));

	// o_data always reflects fifo at rdaddr
	o_data_reads_rdaddr:     assert property (@(posedge i_clk)
		o_data == sfifo.fifo[sfifo.rdaddr[LGFLEN-1:0]]);

	// Full FIFO stays full when no read
	full_stable_no_read:     assert property (@(posedge i_clk) disable iff (i_reset)
		(o_full && !i_rd) |=> o_full);

	// Empty FIFO stays empty when no write
	empty_stable_no_write:   assert property (@(posedge i_clk) disable iff (i_reset)
		(o_empty && !i_wr) |=> o_empty);

	// A write to non-full FIFO clears empty
	write_clears_empty:      assert property (@(posedge i_clk) disable iff (i_reset)
		(!o_full && i_wr) |=> !o_empty);

endmodule

bind sfifo sfifo_assert #(.DW(DW), .LGFLEN(LGFLEN)) sfifo_assert_instance (.*);
