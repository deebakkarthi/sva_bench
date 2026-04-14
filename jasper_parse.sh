#!/usr/bin/env bash

progname=$(basename "$0")


function usage() {
	echo -ne "Usage: $progname DIR [-h]\n"\
	"Parse jgoutput folder and extract metrics.\n"\
	"-h\tPrint this help message\n"\
	"DIR\ta jgoutput folder\n"
}

if [[ $# -ne 1 ]]; then
	echo "$progname: Invalid commandline arguments"
	usage
	exit 1
fi

if [[ "$1" == "-h" ]];then
	usage
	exit 0
fi

jgoutput_dir=$1

# check if dir exists
if [[ ! -d $jgoutput_dir ]]; then
	echo "$progname: $jgoutput_dir doesn't exist"
	exit 1
fi

jglog_file="$jgoutput_dir/jg.log"
# check of jg.log file
if [[ ! -f "$jglog_file" ]]; then
	echo "$progname: $jgoutput_dir/jg.log doesn't exist"
	exit 1
fi


# Use sed to grab stuff
# properties is the second line from /^SUMMARY$/
cat $jglog_file | grep "^SVABENCH"
