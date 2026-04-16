#!/usr/bin/env bash
# 
# script just columnates the output of scripts/cat_results.sh
# cat_results.sh does its processesing file by file, hence making
# it impossible to columnate everything.

progname=$(basename $0)

function usage() {
	echo -ne "Usage: $progname [DIR|-h]\n\
 DIR\tA directory under results.\n\
    \tIf not given the most recent dir under results is used.\n\
 -h\tPrint this help message\n"
}

if [[ $# -gt 1 ]]; then
	echo "$progname: Invalid commandline args"
	usage
	exit 1
fi

if [[ $1 == "-h" ]]; then
	usage
	exit 0
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


$SVABENCH_ROOT/scripts/cat_results.sh $results_dir | column -t -s ';' -o '|'
exit 0
