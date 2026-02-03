#!/usr/bin/env bash
#
# Iterates through all the command files (*.f) in the bench/ directory
# and finds out if they are syntactically correct

# Allows for the script to be run both as ./scripts/check_command_files.sh or ./check_command_files.sh
if [ -z $SVABENCH_ROOT ]; then
	export SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi

readarray -t files <<< $(find $SVABENCH_ROOT/bench/ -name '*.f' -type f)
total=${#files[@]}
success=0
for index in "${!files[@]}"; do
	printf "[$(( index+1 ))/$total] Compiling $(basename ${files[$index]})"
	iverilog -o /dev/null -f "${files[$index]}"  >> /dev/null 2>&1
	if [ "$?" -eq "0" ]; then
		printf "\tPASSED\n"
	else
		printf "\tFAILED\n"
		$success=1
	fi
done
exit $success
