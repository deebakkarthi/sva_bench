clear -all

analyze -sv -f apbi2c.f
analyze -sv -f apbi2c_sva.f
check_cov -init -model all -type mutation

elaborate

clock PCLK
reset PRESETn

prove -all

check_cov -measure -bg
