#!/usr/bin/env bash

progname=$(basename $0)

function usage() {
	echo -ne "Usage: $progname [DIR]\n\
 DIR\tA directory under results/.
    \tIf not given the most recent dir under results is used.\n"
}

function get_top_level_dirs(){
	find $1 -depth -mindepth 1 -maxdepth 1 -type d
}

if [[ $# -gt 1 ]]; then
	echo "$progname: Invalid commandline args"
	usage
	exit 1
fi


if [ -z "$SVABENCH_ROOT" ]; then
        log "\$SVABENCH_ROOT is not set"
        log "Setting it using git rev-parse --show-toplevel"
        SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi
SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)

if [[ ! -z $1 ]]; then
	results_dir=$1
else
	results_dir=$($SVABENCH_ROOT/scripts/most_recent_result.sh)
fi

if [[ ! -d $results_dir ]]; then
	echo "$progname: $results_dir doesn't exist"
	exit 1
fi


echo -e "Benchmark;Total Assertions;Proven;CEX;Covered;Proven and Covered;Formal Coverage"
for benchmark_path in $(get_top_level_dirs $results_dir); do
	benchmark_name=$(basename $benchmark_path)
	echo -ne "$benchmark_name;"
	$SVABENCH_ROOT/jasper_parse.sh $benchmark_path/jgproject | awk -F":" '{printf "%s;", $3}'
	echo ""
done
