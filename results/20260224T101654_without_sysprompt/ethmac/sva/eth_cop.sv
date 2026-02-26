module eth_cop_sva (
    wb_clk_i, wb_rst_i,
    m1_wb_adr_i, m1_wb_sel_i, m1_wb_we_i,  m1_wb_dat_o,
    m1_wb_dat_i, m1_wb_cyc_i, m1_wb_stb_i, m1_wb_ack_o,
    m1_wb_err_o,
    m2_wb_adr_i, m2_wb_sel_i, m2_wb_we_i,  m2_wb_dat_o,
    m2_wb_dat_i, m2_wb_cyc_i, m2_wb_stb_i, m2_wb_ack_o,
    m2_wb_err_o,
    s1_wb_adr_o, s1_wb_sel_o, s1_wb_we_o,  s1_wb_cyc_o,
    s1_wb_stb_o, s1_wb_ack_i, s1_wb_err_i, s1_wb_dat_i,
    s1_wb_dat_o,
    s2_wb_adr_o, s2_wb_sel_o, s2_wb_we_o,  s2_wb_cyc_o,
    s2_wb_stb_o, s2_wb_ack_i, s2_wb_err_i, s2_wb_dat_i,
    s2_wb_dat_o
);

parameter ETH_BASE     = 32'hd0000000;
parameter ETH_WIDTH    = 32'h800;
parameter MEMORY_BASE  = 32'h2000;
parameter MEMORY_WIDTH = 32'h10000;

input         wb_clk_i, wb_rst_i;
input  [31:0] m1_wb_adr_i, m1_wb_dat_i;
input   [3:0] m1_wb_sel_i;
input         m1_wb_cyc_i, m1_wb_stb_i, m1_wb_we_i;
input  [31:0] m1_wb_dat_o;
input         m1_wb_ack_o, m1_wb_err_o;
input  [31:0] m2_wb_adr_i, m2_wb_dat_i;
input   [3:0] m2_wb_sel_i;
input         m2_wb_cyc_i, m2_wb_stb_i, m2_wb_we_i;
input  [31:0] m2_wb_dat_o;
input         m2_wb_ack_o, m2_wb_err_o;
input  [31:0] s1_wb_dat_i;
input         s1_wb_ack_i, s1_wb_err_i;
input  [31:0] s1_wb_adr_o, s1_wb_dat_o;
input   [3:0] s1_wb_sel_o;
input         s1_wb_we_o, s1_wb_cyc_o, s1_wb_stb_o;
input  [31:0] s2_wb_dat_i;
input         s2_wb_ack_i, s2_wb_err_i;
input  [31:0] s2_wb_adr_o, s2_wb_dat_o;
input   [3:0] s2_wb_sel_o;
input         s2_wb_we_o, s2_wb_cyc_o, s2_wb_stb_o;

wire m1_addressed_s1 = (m1_wb_adr_i >= ETH_BASE) &
                       (m1_wb_adr_i < (ETH_BASE + ETH_WIDTH));
wire m1_addressed_s2 = (m1_wb_adr_i >= MEMORY_BASE) &
                       (m1_wb_adr_i < (MEMORY_BASE + MEMORY_WIDTH));
wire m2_addressed_s1 = (m2_wb_adr_i >= ETH_BASE) &
                       (m2_wb_adr_i < (ETH_BASE + ETH_WIDTH));
wire m2_addressed_s2 = (m2_wb_adr_i >= MEMORY_BASE) &
                       (m2_wb_adr_i < (MEMORY_BASE + MEMORY_WIDTH));

int shadow_cnt;
always @(posedge wb_clk_i or posedge wb_rst_i) begin
    if (wb_rst_i)
        shadow_cnt <= 0;
    else if (s1_wb_ack_i | s1_wb_err_i | s2_wb_ack_i | s2_wb_err_i)
        shadow_cnt <= 0;
    else if (s1_wb_cyc_o | s2_wb_cyc_o)
        shadow_cnt <= shadow_cnt + 1;
end

reset_clears_s1_cyc : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s1_wb_cyc_o);

reset_clears_s1_stb : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s1_wb_stb_o);

reset_clears_s2_cyc : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s2_wb_cyc_o);

reset_clears_s2_stb : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s2_wb_stb_o);

reset_clears_s1_we : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s1_wb_we_o);

reset_clears_s2_we : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> !s2_wb_we_o);

reset_clears_s1_adr : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s1_wb_adr_o == 32'b0));

reset_clears_s2_adr : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s2_wb_adr_o == 32'b0));

reset_clears_s1_sel : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s1_wb_sel_o == 4'b0));

reset_clears_s2_sel : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s2_wb_sel_o == 4'b0));

reset_clears_s1_dat : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s1_wb_dat_o == 32'b0));

reset_clears_s2_dat : assert property (@(posedge wb_clk_i)
    wb_rst_i |=> (s2_wb_dat_o == 32'b0));

slave_cyc_mutual_exclusion : assert property (@(posedge wb_clk_i)
    !(s1_wb_cyc_o & s2_wb_cyc_o));

s1_stb_iff_cyc : assert property (@(posedge wb_clk_i)
    s1_wb_cyc_o == s1_wb_stb_o);

s2_stb_iff_cyc : assert property (@(posedge wb_clk_i)
    s2_wb_cyc_o == s2_wb_stb_o);

m1_ack_implies_slave_ack : assert property (@(posedge wb_clk_i)
    m1_wb_ack_o |-> (s1_wb_ack_i | s2_wb_ack_i));

m2_ack_implies_slave_ack : assert property (@(posedge wb_clk_i)
    m2_wb_ack_o |-> (s1_wb_ack_i | s2_wb_ack_i));

m1_ack_err_mutex : assert property (@(posedge wb_clk_i)
    !(m1_wb_ack_o & m1_wb_err_o));

m2_ack_err_mutex : assert property (@(posedge wb_clk_i)
    !(m2_wb_ack_o & m2_wb_err_o));

masters_ack_mutex : assert property (@(posedge wb_clk_i)
    !(m1_wb_ack_o & m2_wb_ack_o));

no_ack_without_slave_cyc : assert property (@(posedge wb_clk_i)
    (!s1_wb_cyc_o & !s2_wb_cyc_o) |-> (!m1_wb_ack_o & !m2_wb_ack_o));

m1_err_on_unaddressed_access : assert property (@(posedge wb_clk_i)
    (m1_wb_cyc_i & m1_wb_stb_i & !m1_addressed_s1 & !m1_addressed_s2) |-> m1_wb_err_o);

m2_err_on_unaddressed_access : assert property (@(posedge wb_clk_i)
    (m2_wb_cyc_i & m2_wb_stb_i & !m2_addressed_s1 & !m2_addressed_s2) |-> m2_wb_err_o);

m1_dat_routing_from_s1 : assert property (@(posedge wb_clk_i)
    (m1_wb_ack_o & s1_wb_cyc_o) |-> (m1_wb_dat_o == s1_wb_dat_i));

m1_dat_routing_from_s2 : assert property (@(posedge wb_clk_i)
    (m1_wb_ack_o & s2_wb_cyc_o) |-> (m1_wb_dat_o == s2_wb_dat_i));

m2_dat_routing_from_s1 : assert property (@(posedge wb_clk_i)
    (m2_wb_ack_o & s1_wb_cyc_o) |-> (m2_wb_dat_o == s1_wb_dat_i));

m2_dat_routing_from_s2 : assert property (@(posedge wb_clk_i)
    (m2_wb_ack_o & s2_wb_cyc_o) |-> (m2_wb_dat_o == s2_wb_dat_i));

s1_address_in_eth_range : assert property (@(posedge wb_clk_i)
    s1_wb_cyc_o |-> (s1_wb_adr_o >= ETH_BASE && s1_wb_adr_o < (ETH_BASE + ETH_WIDTH)));

s2_address_in_memory_range : assert property (@(posedge wb_clk_i)
    s2_wb_cyc_o |-> (s2_wb_adr_o >= MEMORY_BASE && s2_wb_adr_o < (MEMORY_BASE + MEMORY_WIDTH)));

m1_no_err_when_not_requested : assert property (@(posedge wb_clk_i)
    (!m1_wb_cyc_i | !m1_wb_stb_i) && !s1_wb_cyc_o && !s2_wb_cyc_o |-> !m1_wb_err_o);

m2_no_err_when_not_requested : assert property (@(posedge wb_clk_i)
    (!m2_wb_cyc_i | !m2_wb_stb_i) && !s1_wb_cyc_o && !s2_wb_cyc_o |-> !m2_wb_err_o);

activity_counter_never_overflows : assert property (@(posedge wb_clk_i)
    shadow_cnt < 1000);

s1_cyc_deasserts_after_ack : assert property (@(posedge wb_clk_i)
    (s1_wb_cyc_o & s1_wb_ack_i) |=> !s1_wb_cyc_o);

s1_cyc_deasserts_after_err : assert property (@(posedge wb_clk_i)
    (s1_wb_cyc_o & s1_wb_err_i) |=> !s1_wb_cyc_o);

s2_cyc_deasserts_after_ack : assert property (@(posedge wb_clk_i)
    (s2_wb_cyc_o & s2_wb_ack_i) |=> !s2_wb_cyc_o);

s2_cyc_deasserts_after_err : assert property (@(posedge wb_clk_i)
    (s2_wb_cyc_o & s2_wb_err_i) |=> !s2_wb_cyc_o);

endmodule

bind eth_cop eth_cop_sva eth_cop_sva_instance (.*);
