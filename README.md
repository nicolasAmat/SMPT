# SMPT

## Install a Compatible Python Environment

The project requires python3. On Windows, you can use ```conda``` to simplify
setting up a new python environment. The project was developped uner a Linux
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
variable.

## Basic Usage for the Tool

```bash
$ python smpt.py -h
usage: smpt.py [-h] [--about] [--version] [-v] [--reduced PATH_PN_REDUCED] [--enumerative PATH_MARKINGS] pn properties

Satisfiability Modulo Petri Net

positional arguments:
  pn                    path to Petri Net (.net format)
  properties            path to Properties (.xml format)

optional arguments:
  -h, --help            show this help message and exit
  --about               dev information
  --version             show program's version number and exit
  -v, --verbose         increase output verbosity
  --reduced PATH_PN_REDUCED
                        Path to reduced Petri Net (.net format)
  --enumerative PATH_MARKINGS
                        Path to markings (.aut format)
```

By default it uses a Bounded-Model Checking approach and try to check a
reachability formula, ```properties```, from a Petri net model written in Tina's
.net syntax.

```bash
$ python smpt.py nets/airplane/airplane.net nets/airplane/GlobalProperties.xml
```

It is also possible to give a reduced version of the net, with option
```--reduced```, obtained with the reduce tool.

```bash
$ python smpt.py --reduced nets/airplane nets/airplane/airplane.net nets/airplane/GlobalProperties.xml
```

## GitHub

To solve a problem when pushing on Github I needed to change my user.email
property just for the repo. My Github 'noreply' email address is
2209941+dalzilio@users.noreply.github.com.

```bash
$ git config  user.email "2209941+dalzilio@users.noreply.github.com"
```

