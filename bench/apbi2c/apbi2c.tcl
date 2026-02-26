clear -all

analyze -v2k -f apbi2c.f
analyze -sv -f apbi2c_sva.f

elaborate

clock PCLK
reset PRESETn

prove -all

llength [get_property_list -include {type {assert} status {proven} related_cover_status {green white}}]
