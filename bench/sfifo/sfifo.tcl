# AUTO-GENERATED USING gen_tcl.sh
# PLEASE CHANGE clock and reset to the appropriate signals

clear -all

analyze -v2k -f sfifo.f
analyze -sv -f sfifo_sva.f

elaborate

clock i_clk
reset -none

prove -all
