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

command_file="$design_dir/${dut}.f"
top_module=$(iverilog -o /dev/null  -f "$command_file" -v  2>/dev/null  | sed -n  '/^LOCATING TOP-LEVEL MODULES$/{n;p}')
echo $top_module




