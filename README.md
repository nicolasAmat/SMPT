# SMPT (Satisfiability Modulo PeTri Net)

## Install a Compatible Python Environment

The project requires python3. On Windows, you can use ```conda``` to simplify
setting up a new python environment. The project was developped under a Linux
environment but also works with Windows System on Linux (WSL).

```bash
$ conda create -n smpn python=3
```

To activate this environment, use
```bash
$ conda activate smpn
```

## Download a SMT Solver

We work with Z3 and use the supported release for the last Ubuntu LTS version,
namely Z3 4.4.1. The executable ```z3.exe``` should be on the PATH environment
variable. The tool is also compatible with the latest stable version 4.8.7 of Z3.

## Basic Usage for the Tool

```bash
$ python smpt.py -h
usage: smpt.py [-h] [--version] [-v] [--debug]
               [--auto-reduce | --reduced PATH_PN_REDUCED]
               [--auto-enumerative | --enumerative PATH_MARKINGS]
               [--timeout TIMEOUT]
               pn properties

Satisfiability Modulo Petri Net

positional arguments:
  pn                    path to Petri Net (.net format)
  properties            path to Properties (.xml format)

optional arguments:
  -h, --help            show this help message and exit
  --version             show program's version number and exit
  -v, --verbose         increase output verbosity
  --debug               display the SMT-LIB input/ouput
  --auto-reduce         reduce automatically the Petri Net (using `reduce`)
  --reduced PATH_PN_REDUCED
                        path to reduced Petri Net (.net format)
  --auto-enumerative    enumerate automatically the states (using `tina`)
  --enumerative PATH_MARKINGS
                        Path to markings (.aut format)
  --timeout TIMEOUT     configure the timeout
```

By default it uses a Bounded-Model Checking approach and try to check a
reachability formula, ```properties```, from a Petri net model written in Tina's
.net syntax.

```bash
$ python smpt.py nets/airplane/airplane.net nets/airplane/GlobalProperties.xml
```

It is also possible to give a reduced version of the net, with option
```--reduced```, obtained with the reduce tool or use ```--auto-reduce``` to automatically generate the reduced net (**requirement**: ```reduce``` on the PATH environment).

```bash
$ python smpt.py --reduced nets/airplane nets/airplane/airplane.net nets/airplane/GlobalProperties.xml
```

```bash
$ python smpt.py --auto-reduce nets/airplane/airplane.net nets/airplane/GlobalProperties.xml
```

## GitHub

To solve a problem when pushing on Github I needed to change my user.email
property just for the repo. My Github 'noreply' email address is
2209941+dalzilio@users.noreply.github.com.

```bash
$ git config  user.email "2209941+dalzilio@users.noreply.github.com"
```

