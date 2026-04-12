clear -all

analyze -v2k -f apbi2c.f
analyze -sv -f apbi2c_sva.f
check_cov -init -type mutation

elaborate

clock PCLK
reset -none

prove -all

llength [get_property_list -include {type {assert} status {proven} related_cover_status {green white}}]
check_cov -measure
check_cov -report
