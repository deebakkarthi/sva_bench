# AUTO-GENERATED USING gen_tcl.sh
# PLEASE CHANGE clock and reset to the appropriate signals

clear -all

analyze -v2k -f counter.f
analyze -sv -f counter_sva.f

elaborate

clock i_clk
reset -none

prove -all
