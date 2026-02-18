#!/usr/bin/env bash

progname=$(basename $0)

function usage(){
	echo -e "Usage: $progname BENCHMARK [-o FOLDER]\n\
 BENCHMARK\n\
\tA folder under /bench which has rtl files at /bench/BENCHMARK/rtl\n\
 -o FOLDER\n\
 \tOutput Folder path\n\
 \tDefaults to /bench/BENCHMARK/sva"
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
# if -o is not given default to bench/BENCHMARK/sva
if [ ! -z $2 ];then
	if [ $2 == "-o" ]; then
		# If -o has an arg use that else error out
		if [ ! -z $3 ]; then
			output_dir=$3
		else
			usage
			exit 1
		fi
	# if other flags are given error out
	else
		usage
		exit 1
	fi
else
	output_dir="$SVABENCH_ROOT/bench/$benchmark/sva"
fi

input_dir="$SVABENCH_ROOT/bench/$benchmark/rtl"

# Check dir exists
if [ ! -d "$input_dir" ]; then
	echo "$progname: $input_dir doesn't exist"
	exit 1
fi

# create output dir
if [ ! -d "$output_dir" ]; then
	mkdir -p $output_dir
else
	if [ ! -z "$(ls -A $output_dir)" ]; then
		echo "$progname: $output_dir is not empty"
		exit 1
	fi
fi

read -r -d '' system_prompt <<'EOF'
Read the following verilog code and generate all systemverilog assertions.
# Output Format
- Output *only* the assertions.
- Don't format using ```systemverilog.
- Don't declare the properties separately. Include them inline with the assertion.
- Give descriptive label for each assertion
The general syntax for systemverilog assertion is
```systemverilog
label : assert property (property_specification);

- Create a new module whose name is the original name suffixed with "_assert"
	- For example, for a module called "half_adder", create another module called "half_adder_assert"
	- The port of the two modules has to be exactly the same.
- Place all of these assertions under that module
- Create a bind construct to bind these two modules. Use implicit port connection syntax.
the name of the module is the name of the assertions module suffixed with "_instance"
Example: 
bind my_module my_module_sva my_module_sva_instance (.*);
```
EOF

readarray files < <( find $input_dir \( -name '*.v' -o -name '*.sv' \) )
for file in ${files[@]}; do
	filename_without_ext=$(basename $file | awk -F"." '{$NF=""; print}' | sed 's/[[:blank:]]*$//' )
	assertions=$(cat $file | claude --print --no-session-persistence --tools ""\
		--model sonnet --no-chrome  --system-prompt "$system_prompt")
	echo "$assertions" > "${output_dir}/${filename_without_ext}.sv"
done

exit $?
