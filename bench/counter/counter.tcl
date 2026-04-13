# AUTO-GENERATED USING gen_tcl.sh
# PLEASE CHANGE clock and reset to the appropriate signals

clear -all

analyze -v2k -f counter.f
analyze -sv -f counter_sva.f
check_cov -init -type mutation

elaborate

clock i_clk
reset -none

prove -all
check_cov -measure
check_cov -report
exit
