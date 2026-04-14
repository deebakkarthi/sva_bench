# AUTO-GENERATED USING gen_tcl.sh
# PLEASE CHANGE clock and reset to the appropriate signals

clear -all

analyze -v2k -f sfifo.f
analyze -sv -f sfifo_sva.f
check_cov -init -type mutation

elaborate

clock i_clk
reset -none

prove -all
puts [format "SVABENCH:Total Assertions: %s" [llength [get_property_list \
-include {type {assert} }]];]

puts [format "SVABENCH:Proven: %s" [llength [get_property_list \
-include {type {assert} status {proven} }]];]

puts [format "SVABENCH:CEX: %s" [llength [get_property_list \
-include {type {assert} status {cex} }]];]

puts [format "SVABENCH:Covered: %s" [llength [get_property_list \
-include {type {assert} related_cover_status {green white} }]];]

puts [format "SVABENCH:Proven and Covered: %s" [llength [get_property_list\
-include {type {assert} status {proven} related_cover_status {green white} }]];]
check_cov -measure
check_cov -report
exit
