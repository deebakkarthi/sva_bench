#!/usr/bin/env bash
#
# Create the directory skeleton expected by svabench

progname=$(basename $0)

function usage()
{
	printf "Usage: $progname BENCHMARK\n"
	printf "\tBENCHMARK is a name of the directory to be placed under ../bench/ \n"
	return
}

if [ "$#" -ne "1" ]; then
	usage
	exit 1
fi

if [ -z "${SVABENCH_ROOT}" ]; then
	export SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi

benchmark=$1
target_dir="${SVABENCH_ROOT}/bench/${benchmark}"
if [[ ! -d "$target_dir"  ]]; then
	mkdir "$target_dir"
else
	# Check if it is not empty
	if [[  ! -z "$( ls -A $target_dir )" ]]; then
		echo "$benchmark dir is not empty"
		exit 1
	fi
fi

mkdir -p "$target_dir/rtl"
touch "$target_dir/$benchmark.f"
touch "$target_dir/$benchmark.tcl"
