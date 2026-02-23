#!/usr/bin/env bash

progname=$(basename $0)

function usage(){
	echo -e "Usage: $progname DIR\n\
 Output a verilog command file with all the files under DIR.  The paths are
 transformed to be a relative path from \$SVABENCH_ROOT
 DIR\n\
\tA directory containing verilog files"
}

if [[ "$#" -lt 1 ]]; then
	usage
	exit 1
fi

input_dir=$(realpath $1)

# Check dir exists
if [ ! -d "$input_dir" ]; then
	echo "$progname: $input_dir doesn't exist"
	exit 1
fi

# This is specifically to deal with blackrock's $HOME which is /var/home
# being mapped to some /net/marysrock.ece.Virginia.EDU/maryisan/users
SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)

echo -n -e "/*AUTO-GENERATED USING $progname*/\n" 
find $input_dir \( -name '*.v' -o -name '*.sv' \) -printf "%p\n" | sed  "s|$SVABENCH_ROOT|\${SVABENCH_ROOT}|"
exit $?
