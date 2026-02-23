#!/usr/bin/env bash

progname=$(basename $0)
_V=0
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

function usage(){
	echo -e "Usage: $progname [-o FOLDER] [-v]\n\
 -o FOLDER\n\
 \tOutput Folder path\n\
 \tDefaults to \$SVABENCH_ROOT/results/
 -v Verbose output"
}

function log(){
	if [[ "$_V" -eq 1 ]]; then
		echo "[INFO] [$(date '+%Y-%m-%d %H:%M:%S')] $*"
	fi
}


# TODO add a cmdline flag to suffix the output dir with some name
# if -o is not given default to $SVABENCH_ROOT/results

while (( "$#" )); do
	case $1 in
		"-o")
			if [ -z $2 ]; then
				output_dir_prefix=$2
				log "-o specified, outputting to $output_dir_prefix"
			else
				usage
				exit 1
			fi
			;;
		"-v")
			_V=1
			;;
		*)
			usage
			exit
			;;
	esac
	shift
done

if [ -z $output_dir_prefix ]; then
	output_dir_prefix="$SVABENCH_ROOT/results"
	log "-o not specified, defaulting output to $output_dir_prefix"
fi

log "Checking if \$SVABENCH_ROOT is set"
if [ -z "$SVABENCH_ROOT" ]; then
	SVABENCH_ROOT=$(git rev-parse --show-toplevel)
	SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)
	log "\$SVABENCH_ROOT is not set"
fi
log "\$SVABENCH_ROOT is set to $SVABENCH_ROOT"


log "\$output_dir_prefix is $output_dir_prefix"

log "Checking if $output_dir_prefix exists, if not creating it"
# create parent dir
if [ ! -d "$output_dir_prefix" ]; then
	mkdir -p $output_dir_prefix
fi

output_dir=$output_dir_prefix/$(date +"%Y%m%dT%H%M%S")
log "Results will be stored under $output_dir"
log "Creating $output_dir"
# create output dir
if [ ! -d "$output_dir" ]; then
	mkdir -p $output_dir
fi


readarray benchmarks < <(find  -L $SVABENCH_ROOT/bench_/ -depth -maxdepth 1\
       	-mindepth 1 -type d)

# Symlink the benchmarks to the results folder
# Each result should be verifiable on its own
# TODO add a cmdline flag to make copies of the files instead of symlinks
for benchmark_path in ${benchmarks[@]}; do
	benchmark=$(basename $benchmark_path)

	mkdir -p $output_dir/$benchmark

	ln -s "$benchmark_path/$benchmark.f"\
	       	"$output_dir/$benchmark/$benchmark.f"

	#mkdir -p "$output_dir/$benchmark/rtl"

	#find $benchmark_path/rtl -type f\
	#       	-exec ln -sf {} $output_dir/$benchmark/rtl/ \;

	rtl_path="$benchmark_path/rtl"

	sva_path="$output_dir/$benchmark/sva"
	log "Creating $sva_path if it doesn't exist"
	if [ ! -d $sva_path ]; then
		mkdir -p $sva_path
	fi

	readarray rtl_files < <( find -L $rtl_path -type f \( -name '*.v' -o -name '*.sv' \) )
	for file in ${rtl_files[@]}; do
		filename_without_ext=$(basename $file | awk -F"." '{$NF=""; print}' | sed 's/[[:blank:]]*$//' )
		log "Processing $benchmark:$(basename $file)"
		log "Prompting Claude"
		assertions=$(cat $file | claude --print --no-session-persistence --tools ""\
			--model haiku --no-chrome  --system-prompt "$system_prompt")
		echo "$assertions" > "${sva_path}/${filename_without_ext}.sv"
		log "Wrote assertions to $filename_without_ext.sv"
	done
	$SVABENCH_ROOT/scripts/gen_command_file_standalone.sh $sva_path > "$output_dir/$benchmark/${benchmark}_sva.f"
	log "Created command file for the assertions"
done
