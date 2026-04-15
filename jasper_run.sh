#!/usr/bin/env bash

progname=$(basename $0)

_V=0
_FORCE=false

function log(){
	if [[ "$_V" -eq 1 ]]; then
		echo "[INFO] [$(date '+%Y-%m-%d %H:%M:%S')] $*"
	fi
}

function usage(){
	echo -ne "Usage: $progname [-v] [-f] [--dir DIR]\n\
 Run jaspergold on the most recent result/\n\
 -v\tVerbose mode\n\
 -f\tOverwrite previous results\n\
 --dir DIR\tdirectory to use instead of the most recent result\n"
}


while (( $# )); do
	case $1 in
		"-v")
			_V=1
			shift
			;;
		"-f")
			_FORCE=true
			shift
			;;
		"--dir")
			if [[ -z "$2" ]]; then
				echo "$progname: DIR not provided"
				usage
				exit 1
			fi
			results_dir=$(realpath $2)
			if [[ ! -d $results_dir ]];then
				echo "$progname: $results_dir doesn't exit"
				exit 1
			fi

			shift
			shift
			;;
		*)
			usage
			exit 1
	esac
done

log "Checking if \$SVABENCH_ROOT is set"
if [ -z "$SVABENCH_ROOT" ]; then
	log "\$SVABENCH_ROOT is not set"
	log "Setting it using git rev-parse --show-toplevel"
	SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi
SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)
log "\$SVABENCH_ROOT is set to $SVABENCH_ROOT"

# No results_dir provided. Use the most recent result
if [[ -z $results_dir ]];then
	results_dir=$($SVABENCH_ROOT/scripts/most_recent_result.sh)
fi

readarray benchmarks < <(find -L $results_dir -depth -maxdepth 1\
	-mindepth 1 -type d)

for benchmark in ${benchmarks[@]};do
	cd "$benchmark"
	base=$(basename $benchmark)
	if [[ -d "$benchmark/jgproject" && $_FORCE = false ]]; then
		echo -e "$progname: jgprojects exits under $base. Use -f to overwrite"
		exit 1
	fi
	# Remove dir to avoid open lock
	rm -rf "$benchmark/jgproject"
	jg -batch -tcl ./"$base".tcl
done
