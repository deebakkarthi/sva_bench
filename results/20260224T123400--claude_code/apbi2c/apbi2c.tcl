clear -all

analyze -sv -f apbi2c.f
analyze -sv -f apbi2c_sva.f

elaborate

clock PCLK
reset PRESETn

prove -all
