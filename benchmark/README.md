# SMPT: Benchmarking Toolset

`SMPT/benchmark/` provides a set of scripts to perform a performance evaluation of the SMPT model-checker.

## Usage

- `install_inputs.sh`  
  Script to download models and properties from the MCC2020, as well as some oracles provided by Yann Thierry-Mieg.  
  Creates `INPUTS/` and `oracle/` directories.

- `run_reductions.sh <path_to_instance_list>`  
  Script to reduce a given list of instances.  
  Saves reduced nets to the `INPUTS/` directory and writes SMPT outputs to the `OUTPUTS/` directory. 

- `run_analysis.sh <path_to_instance_list>`  
  Script to analyze `ReachabilityCardinality`, `ReachabilityFireability` and `ReachabilityDeadlock` properties
  for a given list of instances.  
  Writes SMPT outputs in the `OUTPUTS/` directory.

- `out2csv.py <path_to_OUTPUTS_dir> <path_to_oracle_dir> [--merge-files]`  
  Sript to summarize `.out` files to `.csv` format.  
  Enable option `--merge-files` to merge all `.csv` files in the `merged/` subdirectory.

- `experimental_results.ipynb`  
  Jupyter notebook to analyze output results.  
  Dependencies:  `notebook`, `pandas`, `numpy`, `matplotlib`, `seaborn`. 

- `instance_lists/`  
  Lists of instances as follows:
  + `instances_all`: all instances,
  + `instances_30-49`: selection of 55 instances with a reduction ratio between 30% and 49%,
  + `instances_50-100`: selection of 179 instances with a reduction ratio between 50% and 100%,
  + `instances_selection`: short selection of instances from `instances_30-49` and `instances_50-100` (only one instance per model).  
  
- `fast_check.sh <path_to_instance_list>`  
  Run `install_inputs.sh`, `run_reductions.sh`, `run_analysis.sh` and `experimental_results.ipynb` consecutively on a given list of instances.

- `run_analysis_sequential.sh <path_to_instance_list>`  
  Similar to `run_analysis.sh` without SMPT parallel executions (for weak hardware configurations).

- `fast_check_sequential.sh <path_to_instance_list>`  
  Similar to `fast_check.sh` without SMPT parellel executions (for weak hardware configurations).
  
## Example

Run complete experiments:
```
$> ./install_inputs.sh
$> ./run_reductions.sh instance_lists/instances_all
$> ./run_analysis.sh instance_lists/instances_30-50
$> ./run_analysis.sh instance_lists/instances_50-100
$> ./out2csv.py OUTPUTS/ oracle/ --merge-files
$> jupyter notebook

# Open the output URL in a web browser.
# Open `experimental_results.ipynb` notebook.
# Click on `Cell -> Run all`.
```

Run fast experiments:
```
$> ./install_inputs.sh
$> echo "<instance_name>" > list; ./fast_check.sh list; rm list

# Open the output URL in a web browser.
# Open `experimental_results.ipynb` notebook.
# Click on `Cell -> Run all`.
```
