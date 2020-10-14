# SMPT: Benchmarking Toolset

`SMPT/benchmark` provides a set of scripts to perform a performance evaluation of the SMPT model-checker.

## Usage

- `install_inputs.sh`  
  Script to download models and properties from the MCC2020, as well as some oracles provided by Yann Thierry-Mieg.  
  Create `INPUTS/` and `oracle/` directories.

- `run_reductions.sh <path_to_instance_list>`  
  Script to reduce a given list of instances.  
  Save reduced nets to the `INPUTS/` directory and write SMPT outputs to the `OUTPUTS/` directory. 

- `run_analysis.sh <path_to_instance_list>`  
  Script to analyze ReachabilityCardinality, ReachablityFireability and ReacahbilityDeadlock properties
  for a given list of instances.  
  Write SMPT outputs in the `OUTPUTS/` directory.

- `out2csv.py <path_to_OUTPUTS_dir> <path_to_oracle_dir> [--merge-files]`  
  Sript to summarize `.out` files to `.csv` format.  
  Enable option `--merge-files` to merge all `.csv` files in the `merged/` subdirectory.

- `experimental_results.ipynb`  
  Jupyter notebook to analyze outputs results.  
  Dependencies: notebook, pandas, numpy, matplotlib, seaborn. 

- `instance_lists/`  
  Lists of instances as follows:
  + `instances_all`: all instances,
  + `instances_30-49`: selection of 55 instances with a reduction ratio between 30% and 49%,
  + `instances_50-100`: selection of 179 instances with a reduction ratio between 50% and 100%. 
  
- `fast_check.sh <path_to_instance_list>`  
  Run `install_inputs.sh`, `run_reductions.sh`, `run_analysis.sh` and `experimental_results.ipynb` consecutively on a given list of instances.

## Example

Complete experiments:
```bash
$> ./install_inputs.sh
$> ./run_reductions.sh instance_lists/instances_all
$> ./run_analysis.sh instance_lists/instances_30-50
$> ./run_analysis.sh instance_lists/instances_50-100
$> ./out2csv.py OUTPUTS/ oracle/ --merge-files
$> jupyter notebook experimental_results.ipynb
```

Fast experiment:
```bash
$> ./install_inputs.sh
$> echo "<instance_name>" > list; ./fast_check.sh list; rm list
```


