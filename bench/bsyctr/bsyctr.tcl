# AUTO-GENERATED USING gen_tcl.sh
# PLEASE CHANGE clock and reset to the appropriate signals

clear -all

analyze -v2k -f bsyctr.f

elaborate

clock i_clk
reset -none

prove -all
