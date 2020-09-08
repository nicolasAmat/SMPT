# SMPT - *Satisfiability Modulo Petri Net*

```
            _____                    _____                    _____                _____
           /\    \                  /\    \                  /\    \              /\    \
          /::\    \                /::\____\                /::\    \            /::\    \
         /::::\    \              /::::|   |               /::::\    \           \:::\    \
        /::::::\    \            /:::::|   |              /::::::\    \           \:::\    \
       /:::/\:::\    \          /::::::|   |             /:::/\:::\    \           \:::\    \
      /:::/__\:::\    \        /:::/|::|   |            /:::/__\:::\    \           \:::\    \
      \:::\   \:::\    \      /:::/ |::|   |           /::::\   \:::\    \          /::::\    \
    ___\:::\   \:::\    \    /:::/  |::|___|______    /::::::\   \:::\    \        /::::::\    \
   /\   \:::\   \:::\    \  /:::/   |::::::::\    \  /:::/\:::\   \:::\____\      /:::/\:::\    \
  /::\   \:::\   \:::\____\/:::/    |:::::::::\____\/:::/  \:::\   \:::|    |    /:::/  \:::\____\
  \:::\   \:::\   \::/    /\::/    / -----/:::/    /\::/    \:::\  /:::|____|   /:::/    \::/    /
   \:::\   \:::\   \/____/  \/____/      /:::/    /  \/_____/\:::\/:::/    /   /:::/    / \/____/
    \:::\   \:::\    \                  /:::/    /            \::::::/    /   /:::/    /
     \:::\   \:::\____\                /:::/    /              \::::/    /   /:::/    /
      \:::\  /:::/    /               /:::/    /                \::/____/    \::/    /
       \:::\/:::/    /               /:::/    /                  --           \/____/
        \::::::/    /               /:::/    /
         \::::/    /               /:::/    /
          \::/    /                \::/    /
           \/____/                  \/____/
```

## About

SMPT is an SMT-based model-checker that takes advantage of nets reduction.

## Requirements

* Python >= 3.5
* [Z3](https://github.com/Z3Prover/z3)

## Running the model-checker

The tool takes as input descriptions in the `.net` format, a textual format for Petri nets described in [the Tina man pages](http://projects.laas.fr/tina/manuals/formats.html).

SMPT supports the verification of several kind of reachability properties on Petri net. For instance, the following call can be used to check for the existence of deadlocked states on model `Kanban-00002.net`.

```bash
$> python smpt.py --deadlock nets/Kanban/Kanban-00002.net
```

You can list all the available options with option `--help` (see below). The
tool support three main kind of properties:

* Detection of deadlocks, `--deadlock`: is there a reachable marking with no outgoing transitions
* Liveness, `--liveness t`: is there a marking where transition `t` can fire. A property often referred to as *quasi-liveness* in the litterature. You can check the liveness of several transitions at the same time by passing a comma-separated list of transition names: `--liveness t1,...,tn`
* Reachability: `--reachability p`: is there a reachable marking where place `p` is marked (it has at least one token). You can check the reachability of several places at once by passing a comma-separated list of place names: `--reachability p1,...,pn`

To take advantage of possible reductions in the Petri net, you can use option `--reduce <path_to_reduced_net>`. For example:

```bash
$> python smpt.py Kanban-00002.net --reduced Kanban-00002_reduced.net --deadlock
```

Option `--auto-reduce` requires the installation of the `reduce` tool, that is
currently developped by the Vertics team at LAAS-CNRS. The regular distribution
of [TINA](http://projects.laas.fr/tina/) does not contain this tool yet.

You can list all the options by using the *help* option:
```
$> python smpt.py --help
usage: smpt.py [-h] [--version] [-v] [--debug]
               (--xml PATH_PROPERTIES | --deadlock | --liveness LIVE_TRANSITIONS | --reachability REACH_PLACES | --concurrent-places)
               [--compressed-matrix] [--complete-matrix]
               [--auto-reduce | --reduced PATH_PN_REDUCED]
               [--auto-enumerative | --enumerative PATH_MARKINGS]
               [--timeout TIMEOUT]
               pn

Satisfiability Modulo Petri Net

positional arguments:
  pn                    path to Petri Net (.net format)

optional arguments:
  -h, --help            show this help message and exit
  --version             show the version number and exit
  -v, --verbose         increase output verbosity
  --debug               print the SMT-LIB input/ouput
  --xml PATH_PROPERTIES
                        use XML format for properties
  --deadlock            deadlock analysis
  --liveness LIVE_TRANSITIONS
                        liveness analysis (comma separated list of transition names)
  --reachability REACH_PLACES
                        reachibility analysis (comma separated list of place names)
  --auto-reduce         reduce automatically the Petri Net (using `reduce`)
  --reduced PATH_PN_REDUCED
                        path to reduced Petri Net (.net format)
  --auto-enumerative    enumerate automatically the states (using `tina`)
  --enumerative PATH_MARKINGS
                        path to the state-space (.aut format)
  --timeout TIMEOUT     set a limit on execution time
```

## Dependencies

The code repository includes copies of models taken from the [MCC Petri Nets
Repository](https://pnrepository.lip6.fr/) located inside folder  ```./nets```.
These files are included in the repository to be used for benchmarking and
continuous testing.

## License

This software is distributed under the
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html) license.
A copy of the license agreement is found in the [LICENSE](./LICENSE) file.

## Authors

* **Nicolas AMAT** -  [LAAS/CNRS](https://www.laas.fr/)

