#!/usr/bin/env bash
#
# Find the most recently created directory under results/

if [ -z "$SVABENCH_ROOT" ]; then
	log "\$SVABENCH_ROOT is not set"
	log "Setting it using git rev-parse --show-toplevel"
	SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi
SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)

find -L $SVABENCH_ROOT/results/ -depth -maxdepth 1 -mindepth 1 -type d\
	-exec stat --format "%W %n" {} \; | sort -r | head -n 1 |\
	cut -d" " -f 2| xargs realpath

exit 0
