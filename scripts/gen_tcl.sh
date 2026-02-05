#!/usr/bin/env bash

progname=$(basename $0)

function usage () {
	echo -e "Usage: $progname BENCHMARK [-o [FILE]]\n\
 BENCHMARK\n\
\tta folder under /bench to create the .tcl file for.\n\
 -o [FILE]\n\
\tWrite to a file.\n\
\tWrites to /bench/BENCHMARK/BENCHMARK.tcl by default if FILE is not provided."
}

if [ $# -lt 1 ]; then
	usage
	exit 1
fi

if [ -z "$SVABENCH_ROOT" ]; then
	SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi

benchmark=$1
# if -o is not given output to stdout
if [ ! -z $2 ];then
	if [ $2 == "-o" ]; then
		# If -o has an arg use that else use default output file
		if [ ! -z $3 ]; then
			output_file=$3
		else
			output_file="$SVABENCH_ROOT/bench/$benchmark/$benchmark.tcl"
			if [ -s "$output_file" ];then
				echo "$progname: Default output file is not empty"
				exit 1
			fi
		fi
	else
		usage
		exit 1
	fi
else
	output_file="/dev/stdout"
fi


input_dir="${SVABENCH_ROOT}/bench/$benchmark"

if [  ! -d "$input_dir" ]; then
	echo "$progname: $benchmark doesn't exist"
	exit 1
fi


cat > $output_file <<EOF
# AUTO-GENERATED USING $progname

clear -all

analyze -sv -f ${benchmark}.f

elaborate

clock clk
reset reset
EOF
