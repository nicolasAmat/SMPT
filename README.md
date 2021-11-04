# SM(P/)T - *Satisfiability Modulo Petri Net*

```
                                   a8                        8a                    
 ad88888ba   88b           d88    d8'  88888888ba        d8  `8b  888888888888
d8"     "8b  888b         d888   d8'   88      "8b     ,8P'   `8b      88     
Y8,          88`8b       d8'88  d8'    88      ,8P    d8"      `8b     88     
`Y8aaaaa,    88 `8b     d8' 88  88     88aaaaaa8P'  ,8P'        88     88     
  `"""""8b,  88  `8b   d8'  88  88     88""""""'   d8"          88     88     
        `8b  88   `8b d8'   88  Y8,    88        ,8P'          ,8P     88     
Y8a     a8P  88    `888'    88   Y8,   88       d8"           ,8P      88     
 "Y88888P"   88     `8'     88    Y8,  88      8P'           ,8P       88     
                                   "8                        8"                                                                                                       
```

## About

SMPT is an SMT-based model-checker for Petri nets mainly focused on *reachability* problems that takes advantage of *net reductions*. 

## Requirements

* Python >= 3.5
  + [psutil](https://pypi.org/project/psutil/) package
  + (optional) [cx_Freeze](https://pypi.org/project/psutil/) package
* [z3](https://github.com/Z3Prover/z3)
* (optional) [mcc](https://github.com/dalzilio/mcc)
* (optional) [reduce](http://projects.laas.fr/tina/) (not released yet)
  + [struct](http://projects.laas.fr/tina/)
  + [4ti2](https://github.com/4ti2/4ti2) or [LattE integrale](https://github.com/latte-int/latte-distro)
* (optional) [MiniZinc](https://www.minizinc.org/)

## Running the model-checker

### Freezeing

(Optional) The tool can be freezed into executables using [cx_Freeze](https://cx-freeze.readthedocs.io/en/latest/) by running:
```
python3 setup.py build
```

### Input Formats and Properties

The tool takes as input descriptions in `.pnml` format and `.net` format (textual format for Petri nets described in [the Tina man pages](http://projects.laas.fr/tina/manuals/formats.html)).
SMPT supports the verification of several kind of reachability properties on Petri net.
For instance, the following call can be used to check for the existence of deadlocked states on model `Kanban-00002.net`.

```
$> smpt --deadlock nets/Kanban/Kanban-00002.net
```

The tools also supports colored Petri nets. In this case, use the option `--colored` and install the [mcc](https://github.com/dalzilio/mcc) tool.  

The tool supports three main kinds of properties:

* Detection of deadlocks, `--deadlock`: is there a reachable marking with no outgoing transitions.
* Quasi-liveness, `--quasi-liveness t`: is there a reachable marking where transition `t` can fire.
You can check the quasi-liveness of several transitions at the same time by passing a comma-separated list of transition names: `--liveness t1,...,tn`.
* Reachability: `--reachability p`: is there a reachable marking where place `p` is marked (it has at least one token).
You can check the reachability of several places at once by passing a comma-separated list of place names: `--reachability p1,...,pn`.

The tool also supports properties from the [MCC properties format](https://mcc.lip6.fr/pdf/MCC2020-formula_manual.pdf) by using the option `--xml` and indicating the path to the `.xml` properties file.
At this time, the support is restricted to:
+ `--xml GlobalProperties.xml`
+ `--xml ReachabilityCardinality.xml`
+ `--xml ReachabilityFireability.xml`

### Output Format

The tool is compliant with the MCC output format. Some options permits to obtain more information:
+ `--verbose` or `-v`: evolution of the methods
+ `--debug`: input/output SMT-LIB exchanged with the SMT solver
+ `--show-techniques`: method returning the result
+ `--show-time`: execution time
+ `--show-reduction-ratio`: reduction ratio
+ `--show-model`: counterexample if there is one
+ `--check-proof`: certificate of invariance if there is one


### Methods

The tool is composed of different methods:
+ `BMC`: Bounded Model Checking
+ `K-INDUCTION`: k-Induction
+ `PDR-COV`: Property Directed Reachability with state-based generalization
+ `PDR-REACH`: Property Directed Reachability with transition-based generalization
+ `PDR-REACH-SATURATED`: Property Directed Reachability with saturated transition-based generalization
+ `SMT`: SMT solver computation for fully reducible nets
+ `CP`: Constraint programming computation for fully reducible nets

Depending on the input net, SMPT runs a subset of these methods in parallel.  
Use `--methods <method_1> ... <methods_n>` to restrict the methods to be run.

### Polyhedral abstractions

To take advantage of possible reductions in the Petri net, you can use option `--reduce <path_to_reduced_net>`.  
For example:

```
$> smpt Kanban-00002.net --reduced Kanban-00002_reduced.net --deadlock
```
Some exemples of nets with their corresponding reductions are available in `nets/E-Abstraction/`.
Option `--auto-reduce` requires the installation of the `reduce` tool, that is currently developped by the Vertics team at LAAS-CNRS.
The regular distribution of [TINA](http://projects.laas.fr/tina/) does not contain this tool yet.

### Usage

You can list all the options by using the *help* option:
```
$> smpt --help
usage: smpt.py [-h] [--version] [-v] [--debug] [--colored] [--xml PATH_PROPERTIES | --deadlock | --quasi-liveness QUASI_LIVE_TRANSITIONS | --reachability REACHABLE_PLACES] [--auto-reduce | --reduced PATH_PTNET_REDUCED] [--save-reduced-net]
               [--methods [{BMC,K-INDUCTION,PDR-COV,PDR-REACH,PDR-REACH-SATURATED,SMT,CP} [{BMC,K-INDUCTION,PDR-COV,PDR-REACH,PDR-REACH-SATURATED,SMT,CP} ...]] | --auto-enumerative | --enumerative PATH_MARKINGS]
               [--timeout TIMEOUT | --global-timeout GLOBAL_TIMEOUT] [--skip-non-monotonic] [--show-techniques] [--show-time] [--show-reduction-ratio] [--show-model] [--check-proof]
               ptnet

SMPT: Satisfiability Modulo Petri Net

positional arguments:
  ptnet                 path to Petri Net (.net or .pnml format)

optional arguments:
  -h, --help            show this help message and exit
  --version             show the version number and exit
  -v, --verbose         increase output verbosity
  --debug               print the SMT-LIB input/ouput
  --colored             colored input Petri net
  --xml PATH_PROPERTIES
                        use XML format for properties
  --deadlock            deadlock analysis
  --quasi-liveness QUASI_LIVE_TRANSITIONS
                        liveness analysis (comma separated list of transition names)
  --reachability REACHABLE_PLACES
                        reachibility analysis (comma separated list of place names)
  --auto-reduce         reduce automatically the Petri Net (using `reduce`)
  --reduced PATH_PTNET_REDUCED
                        path to reduced Petri Net (.net format)
  --save-reduced-net    save the reduced net
  --methods [{BMC,K-INDUCTION,PDR-COV,PDR-REACH,PDR-REACH-SATURATED,SMT,CP} [{BMC,K-INDUCTION,PDR-COV,PDR-REACH,PDR-REACH-SATURATED,SMT,CP} ...]]
                        enable methods among BMC K-INDUCTION PDR-COV PDR-REACH PDR-REACH-SATURATED SMT CP
  --auto-enumerative    enumerate automatically the states (using `tina`)
  --enumerative PATH_MARKINGS
                        path to the state-space (.aut format)
  --timeout TIMEOUT     a limit per property on execution time
  --global-timeout GLOBAL_TIMEOUT
                        a limit on execution time
  --skip-non-monotonic  skip non-monotonic properties
  --show-techniques     show the method returning the result
  --show-time           show the execution time
  --show-reduction-ratio
                        show the reduction ratio
  --show-model          show a counterexample if there is one
  --check-proof         check and show the certificate of invariance if there is one
```

## References

+ Nicolas Amat, Bernard Berthomieu, Silvano Dal Zilio. On the Combination of Polyhedral Abstraction 
and SMT-based Model Checking for Petri nets. *42rd International Conference on Application and 
Theory of Petri Nets and Concurrency (Petri Nets 2021)*, Jun 2021, Paris (virtual), France. 
+ F. Kordon and P. Bouvier and H. Garavel and L. M. Hillah and F. Hulin-Hubard and
	N. Amat. and E. Amparore and B. Berthomieu and S. Biswal and D. Donatelli and
	F. Galla and and S. Dal Zilio and P. G. Jensen and  C. He and
	D. Le Botlan and S. Li and and J. Srba and . Thierry-Mieg and 
	A. Walner and K. Wolf, Complete Results for the 2021 Edition of the Model Checking Contest, June 2021.

## Dependencies

The code repository includes copies of models taken from the [MCC Petri Nets
Repository](https://pnrepository.lip6.fr/) located inside folder  ```./nets```.

## License

This software is distributed under the
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html) license.
A copy of the license agreement is found in the [LICENSE](./LICENSE) file.

## Authors

* **Nicolas AMAT** -  [LAAS/CNRS](https://www.laas.fr/)
* **Bernard BERTHOMIEU** - [LAAS/CNRS](https://www.laas.fr/)
* **Silvano DAL ZILIO** - [LAAS/CNRS](https://www.laas.fr/)
* **Didier LE BOTLAN** - [LAAS/CNRS](https://www.laas.fr/)

We are grateful to Yann THIERRY-MIEG for making [MCC'2020 oracles](https://github.com/yanntm/pnmcc-models-2020) available.

