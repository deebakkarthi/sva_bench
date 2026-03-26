#!/usr/bin/env bash

progname=$(basename $0)

_V=0
_MODEL="sonnet"


read -r -d '' system_prompt <<'EOF'
You are an expert Hardware Verification Engineer.
The design hierarchy is as follows
i2c (i2c)
|-> DUT_FIFO_TX (fifo)
|-> DUT_FIFO_RX (fifo)
|-> DUT_APB (apb)
|-> DUT_I2C_INTERNAL_RX_TX (module_i2c)

Don't generate assertion for the input signals of the top module (i2c).
Keep the design hierarchy in mind while generating the assertions.
EOF

read -r -d '' prompt <<'EOF'
Read the following verilog code and generate all systemverilog assertions.

# Output Format
- The general syntax for systemverilog assertion is
```systemverilog
label : assert property (property_specification);
```
- Output *only* the assertions. No need to explain them.
- Don't format using the ```systemverilog``` block. I have formatted the instructions 
with them to clearly demarcate the code to you. You don't need to do that. Output only the raw code. 
What you output will be piped directly a ".sv" file. Hence only output syntactically 
correct systemverilog tokens.
- Don't declare the properties separately. Include them inline with the assertion.
	- *Don't * do this
	```systemverilog
	  property handshake;
	    @(posedge Clock) request |-> acknowledge;
	  endproperty
	  assert property (handshake);
	```
	- *Do* this
	```systemverilog
	handshake: assert property (@(posedge Clock) request |-> acknowledge);
	```
- Give descriptive label for each assertion
- Output only `assert`. Don't output `cover` or `assume`.
- Create a new module whose name is the original name suffixed with "_assert"
	- For example, for a module called "half_adder", create another module called "half_adder_assert"
	- The assertion module must only contain input ports. All ports from the original module
	(whether declared as input or output) must be declared as input in the assertion module.
	Assertion modules only observe signals; they never drive outputs.
- Place all of these assertions under that module
- Create a bind construct to bind these two modules. Use implicit port connection syntax.
the name of the module is the name of the assertions module suffixed with "_instance"
Example: 
bind my_module my_module_sva my_module_sva_instance (.*);
- If you want to reference internal items use hierarchical access.
If you want to access an internal item called "RX_FULL" in the module "my_module",
use "my_module.RX_FULL" when you are writing "my_module_assert".
Don't use "my_module_assert_instance.RX_FULL" or "my_module_assert.RX_FULL". 
Both of these are wrong. Access from the original module given as input.

## Complete Example
Lets suppose the following verilog as an example input
```verilog
module fulladd (  input [3:0] a,
                  input [3:0] b,
                  input c_in,
                  output c_out,
                  output [3:0] sum);

   assign {c_out, sum} = a + b + c_in;
endmodule
```
Output something like this
```systemverilog
module fulladd_assert (  input [3:0] a,
                  input [3:0] b,
                  input c_in,
                  input c_out,
                  input [3:0] sum);
// ASSERTIONS HERE
endmodule

bind fulladd fulladd_assert fulladd_assert_instance (.*);
```
EOF

function usage(){
	echo -e "Usage: $progname [-o FOLDER] [-v] [-n NAME] [-m MODEL]\n\
 -o FOLDER\n\
 \tOutput Folder path\n\
 \tDefaults to \$SVABENCH_ROOT/results/
 -v Verbose output
 -n Description of the run (Eg: modified_systemprompt)
 -m Model to use. Acceptable models are haiku, sonnet or opus"
}

function log(){
	if [[ "$_V" -eq 1 ]]; then
		echo "[INFO] [$(date '+%Y-%m-%d %H:%M:%S')] $*"
	fi
}

function sanitize_string(){
	echo $1 | sed 's/[[:blank:]]*$//;s/[[:blank:]]\{1,\}/_/g;'  |  tr '[:upper:]' '[:lower:]' | tr -d -C '[:alnum:] _'
}


# TODO add a cmdline flag to suffix the output dir with some name
# if -o is not given default to $SVABENCH_ROOT/results

while (( "$#" )); do
	case $1 in
		"-o")
			if [ ! -z $2 ]; then
				output_dir_prefix=$2
				log "-o specified, outputting to $output_dir_prefix"
				shift
			else
				usage
				exit 1
			fi
			;;
		"-v")
			_V=1
			;;
		"-n")
			if [[ ! -z $2 ]]; then
				output_dir_suffix="$2"
				output_dir_suffix="$(sanitize_string "$output_dir_suffix")"
				log "-n specified, output will be suffixed with $output_dir_suffix"
				shift
			else
				usage
				exit 1
			fi
			;;
		"-m")
			if [[ ! -z "$2" ]]; then
				_MODEL="$2"
			else
				usage
				exit 1
			fi
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
	log "\$SVABENCH_ROOT is not set"
	log "Setting it using git rev-parse --show-toplevel"
	SVABENCH_ROOT=$(git rev-parse --show-toplevel)
fi
SVABENCH_ROOT=$(realpath $SVABENCH_ROOT)
log "\$SVABENCH_ROOT is set to $SVABENCH_ROOT"


log "Output will be stored under $output_dir_prefix"

log "Checking if $output_dir_prefix exists"
# create parent dir
if [ ! -d "$output_dir_prefix" ]; then
	log "$output_dir_prefix doesn't exists, creating it"
	mkdir -p $output_dir_prefix
fi

if [[ ! -z $output_dir_suffix ]];then
	output_dir="$output_dir_prefix/$(date +"%Y%m%dT%H%M%S")--${output_dir_suffix}"
else
	output_dir="$output_dir_prefix/$(date +"%Y%m%dT%H%M%S")"
fi

log "The output is a folder and will be stored under $output_dir"
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
	log "Created symlink to "$benchmark_path/$benchmark.f$""

	ln -s "$benchmark_path/$benchmark.tcl"\
	       	"$output_dir/$benchmark/$benchmark.tcl"
	log "Created symlink to "$benchmark_path/$benchmark.tcl$""

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
		cd "$output_dir/$benchmark"
		log "cd into "$output_dir/$benchmark""

		filename_without_ext=$(basename $file | awk -F"." '{$NF=""; print}' | sed 's/[[:blank:]]*$//' )
		log "Processing $benchmark:$(basename $file)"
		log "Prompting Claude"

		start_time=$SECONDS
		assertions=$(cat $file | claude --continue --print --tools ""\
			--model "${_MODEL}" --no-chrome --system-prompt "$system_prompt" "$prompt")
		end_time=$SECONDS
		log "Claude took $(( end_time - start_time ))s"

		echo "$assertions" > "${sva_path}/${filename_without_ext}.sv"
		log "Wrote assertions to $filename_without_ext.sv"
	done
	$SVABENCH_ROOT/scripts/gen_command_file_standalone.sh $sva_path > "$output_dir/$benchmark/${benchmark}_sva.f"
	log "Created command file for the assertions"
done
