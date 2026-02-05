#!/usr/bin/env bash

progname=$(basename $0)

function usage(){
	echo -e "Usage: $progname BENCHMARK [-o [FILE]]\n\
 BENCHMARK\n\
\tA folder under /bench which has rtl files at /bench/BENCHMARK/rtl\n\
 -o [FILE]\n\
 \tOutput file path\n\
 \tDefaults to /bench/BENCHMARK/BENCHMARK.f"
}

if [[ "$#" -lt 1 ]]; then
	usage
	exit 1
fi

# TODO: Check if $input_dir is just a single word
# if so check if it exists. If it doesn't assume the
# $input_dir to be $SVABENCH_ROOT/bench/$input_dir
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
			output_file="$SVABENCH_ROOT/bench/$benchmark/$benchmark.f"
		fi
	else
		usage
		exit 1
	fi
else
	output_file="/dev/stdout"
fi

input_dir="$SVABENCH_ROOT/bench/$benchmark/rtl"

# Check dir exists
if [ ! -d "$input_dir" ]; then
	echo "$progname: $input_dir doesn't exist"
	exit 1
fi

echo -n -e "/*AUTO-GENERATED USING $progname*/\n" > $output_file
find $input_dir \( -name '*.v' -o -name '*.sv' \) -printf "\${SVABENCH_ROOT}/bench/${benchmark}/rtl/%P\n" >> $output_file
exit $?
