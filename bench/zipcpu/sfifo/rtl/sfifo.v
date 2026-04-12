`default_nettype	none
module sfifo #(
		parameter	DW=8,		// Byte/data width
		parameter	LGFLEN=4	// Log of the buffer size
	) (
		input	wire		i_clk, i_reset,
		input	wire		i_wr,
		input	wire [(DW-1):0]	i_data,
		output	reg		o_full,
		input	wire		i_rd,
		output	wire [(DW-1):0]	o_data,
		output	reg		o_empty,
		output	wire		o_err
	);

	localparam	FLEN=(1<<LGFLEN);

	reg	[(DW-1):0]	fifo[0:(FLEN-1)];
	reg	[LGFLEN:0]	wraddr, rdaddr;

	wire	w_wr = (i_wr && (!o_full || i_rd));
	wire	w_rd = (i_rd && !o_empty);

	wire	[LGFLEN:0]	w_wraddr_plus_one, w_rdaddr_plus_one;
	assign	w_wraddr_plus_one = wraddr + {{(LGFLEN){1'b0}},1'b1};
	assign	w_rdaddr_plus_one = rdaddr  + 1'b1;

	reg		r_ovfl;	// Overflow has taken place
	reg		r_unfl;	// Underflow has taken place

	initial	o_full = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_full <= 1'b0;
	else if (i_rd)
		o_full <= (o_full)&&(i_wr);
	else if (i_wr)
		o_full <= (o_full)
			||((w_wraddr_plus_one[LGFLEN-1:0]
					== rdaddr[LGFLEN-1:0])
			&&(w_wraddr_plus_one[LGFLEN]!=rdaddr[LGFLEN]));
	else if ((wraddr[LGFLEN-1:0] == rdaddr[LGFLEN-1:0])
			&&(wraddr[LGFLEN]!=rdaddr[LGFLEN]))
		o_full <= 1'b1;

	//
	// Adjust the Write pointer, and catch any overflows.
	initial	wraddr = 0;
	initial	r_ovfl  = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_ovfl  <= 1'b0;
		wraddr <= 0;
	end else if (i_wr)
	begin // Cowardly refuse to overflow
		if ((i_rd)||(!o_full))
			wraddr <= wraddr + 1'b1;
		else
			// Set the error flag on any overflow
			r_ovfl <= 1'b1;
	end

	// Actually write to the FIFO
	always @(posedge i_clk)
	if (w_wr)
		fifo[wraddr[(LGFLEN-1):0]] <= i_data;

	initial	o_empty = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_empty <= 1'b1;
	else if (i_wr)
		o_empty <= 1'b0;
	else if (i_rd)
		o_empty <= (o_empty)||(w_rdaddr_plus_one == wraddr);
	else
		o_empty <= (rdaddr == wraddr);

	initial	r_unfl = 1'b0;
	initial	rdaddr = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		rdaddr <= 0;
		r_unfl <= 1'b0;
	end else if (i_rd)
	begin
		if (!o_empty) // (wraddr != rdaddr)
			rdaddr <= rdaddr + 1;
		else
			// Set the error flag on any attempt to read
			// from an empty fifo
			r_unfl <= 1'b1;
	end

	// Actually read from the FIFO here.
	assign	o_data = fifo[rdaddr[LGFLEN-1:0]];

	// Overflow is an error, as is underflow.
	assign o_err = (r_ovfl)||(r_unfl);
endmodule
