module dblpipe_assert (
    input wire i_clk,
    input wire i_ce,
    input wire i_data,
    input wire o_data
);

lfsr_outputs_synchronized: assert property (dblpipe.a_data == dblpipe.b_data);

o_data_always_zero: assert property (o_data == 1'b0);

o_data_pipeline_correct: assert property (@(posedge i_clk) o_data == ($past(dblpipe.a_data) ^ $past(dblpipe.b_data)));

endmodule

bind dblpipe dblpipe_assert dblpipe_assert_instance (.*);
