#!/usr/bin/env bash
#
# Find the top module of a set of verilog files

progname=$(basename $0)

function usage()
{
	printf "Usage: $progname DIR\n"
	printf "\tDIR is a name of a directory under ../bench/ \n"
	return
}

if [ "$#" -ne "1" ]; then
	usage
	exit 1
fi

if [ -z "${SVABENCH_ROOT}" ]; then
        export SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi


dut=$1
design_dir="${SVABENCH_ROOT}/bench/${dut}"
if  [ ! -d  $design_dir ]; then
	printf "$progname: $1 doesn't exist\n"
	exit 1
fi
proj_dir=$(mktemp -d)
command_file="$design_dir/${dut}.f"
top_module=$(jg -no_gui -proj ${proj_dir} -command "clear -all; analyze -sv -f ${command_file}; elaborate ; elaborate -list; exit" | grep "^Main design" | sed 's/Main design//g;s/^[[:space:]]*//;s/[[:space:]]*$//' -)
rm -rf "$proj_dir"
echo $top_module
exit 0
