[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![License](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
[![Documentation Status](https://readthedocs.org/projects/ansicolortags/badge/?version=latest)](https://align-analoglayout.github.io/ALIGN-public/)

# ALIGN: Analog Layout, Intelligently Generated from Netlists

ALIGN is an open source automatic layout generator for analog circuits jointly developed under the DARPA IDEA program by the University of Minnesota, Texas A&M University, and Intel Corporation.

The goal of ALIGN (Analog Layout, Intelligently Generated from Netlists) is to automatically translate an unannotated (or partially annotated) SPICE netlist of an analog circuit to a GDSII layout. The repository also releases a set of analog circuit designs.

The ALIGN flow includes the following steps:
* _Circuit annotation_ creates a multilevel hierarchical representation of the input netlist. This representation is used to implement the circuit layout in using a hierarchical manner.
* _Design rule abstraction_ creates a compact JSON-format represetation of the design rules in a PDK. This repository provides a mock PDK based on a FinFET technology (where the parameters are based on published data). These design rules are used to guide the layout and ensure DRC-correctness.
* _Primitive cell generation_ works with primitives, i.e., blocks at the lowest level of design hierarchy, and generates their layouts. Primitives typically contain a small number of transistor structures (each of which may be implemented using multiple fins and/or fingers). A parameterized instance of a primitive is automatically translated to a GDSII layout in this step.
* _Placement and routing_ performs block assembly of the hierarchical blocks in the netlist and routes connections between these blocks, while obeying a set of analog layout constraints. At the end of this step, the translation of the input SPICE netlist to a GDSII layout is complete.

## Inputs

* A [SPICE netlist](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples/telescopic_ota/telescopic_ota.sp) of the analog circuit
* [Setup file](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples/telescopic_ota/telescopic_ota.setup)
  * Power and Gnd signals (First power signal is used for global power grid)
  * Clk signal (optional)
  * Digital blocks (optional)

* Library:(SPICE format)
  * A basic built-in [template library](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/align/config/basic_template.sp) is provided, which is used to identify hierachies in the design.
  * More library elements can be added in the [user_template library](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/align/config/user_template.sp).

* PDK: Abstracted [design rules](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK)
  * A mock FinFET 14nm PDK [rules file](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK/layers.json) is provided, which is used by the primitive cell generator and the place and route engine.
  * A new PDK can be represented using a JSON-format design rule abstraction, similar to mock-PDK design rules file provided.
  * Primitive cells(NMOS/PMOS/[Resistor](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK/fabric_Res.py)/[Capacitor](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK/fabric_Cap.py)) must be redefined for any new PDK.

* LEF:
  * A list of parameterized cells supported by cell generator is stored in file [param_lef](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/align/config/param_lef).

## Outputs

* Design JSON: Final layout in JSON form which can be viewed using the ALIGN Viewer.
* Layout GDS: Final layout of the design. The output GDS can be imported into any GDSII viewer.

## Getting started

### Step 0: Check prerequisites
The following dependencies must be met by your system:
  * gcc >= 6.1.0 (For C++14 support)
  * python >= 3.7 (For [PEP 560](https://www.python.org/dev/peps/pep-0560/) support)
You may optionally install [Boost](https://www.boost.org/) & [lp_solve](http://lpsolve.sourceforge.net/5.5/) using your distro package manager (apt, yum etc) to save some compilation time.

Note: In case you have multiple gcc versions installed on your system, we recommend explicitly setting the compiler paths as follows:
```console
$ export CC=/path/to/your/gcc
$ export CXX=/path/to/your/g++
```

### Step 1: Clone the ALIGN source code to your local environment
```console
$ git clone https://github.com/ALIGN-analoglayout/ALIGN-public
$ cd ALIGN-public
```

### Step 2: Create a [Python virtualenv](https://docs.python.org/3/tutorial/venv.html)
Note: You may choose to skip this step if you are doing a system-wide install for multiple users.
      Please DO NOT skip this step if you are installing for personal use and/or you are a developer.
```console
$ python -m venv general
$ source general/bin/activate
$ python -m pip install pip --upgrade
```

### Step 3a: Install ALIGN as a USER
If you already have a working installation of Python 3.7 or Python 3.8, the easiest way to install ALIGN is:
```console
$ pip install -v .
```

### Step 3b: Install ALIGN as a DEVELOPER
If you are a developer, you may wish to install align with some additional flags.

For python developers:
```console
$ pip install -e .[test]
```
The `-e` or `--editable` flag generates links to the align package within your current directory. This allows you to modify python files and test them out immediately. You will still need to re-run this command to build your C++ collateral (when you are changing branches for example). More on that below.

For ALIGN (C++) Extension developers:
```console
$ pip install setuptools wheel pybind11 scikit-build cmake ninja
$ pip install -v -e .[test] --no-build-isolation
```
The second command doesn't just install ALIGN inplace, it also caches generated object files etc. under an `_skbuild` subdirectory. Re-running `pip install -v -e .[test] --no-build-isolation` will reuse this cache to perform an incremental build. We add the `-v` or `--verbose` flag to be able to see build flags in the terminal.

If you want the build-type to be Release (-O3), you can issue the following three lines:
```console
$ pip install setuptools wheel pybind11 numpy scikit-build cmake ninja
$ pip install -v -e .[test] --no-build-isolation
$ pip install -v --no-build-isolation -e . --no-deps --install-option='--build-type=Release' --install-option='-DBUILD_TESTING=ON'
```
or
```console
$ pip install setuptools wheel pybind11 numpy scikit-build cmake ninja
$ pip install -v -e .[test] --no-build-isolation
$ pip install -v --no-build-isolation -e . --no-deps --install-option='--build-type=RelWithDebInfo' --install-option='-DBUILD_TESTING=ON'
```
Use the `Release` mode if you are mostly developing in Python and don't need the C++ debugging symbols. Use the `RelWithDebInfo` if you need both debug symbols and optimized code.

To debug runtime issues, run:
```console
python -m cProfile -o stats $ALIGN_HOME/bin/schematic2layout.py $ALIGN_HOME/examples/sc_dc_dc_converter
```
Then in a python shell:
```python
import pstats
from pstats import SortKey
p = pstats.Stats('stats')
p.sort_stats(SortKey.TIME).print_stats(20)
```

To run tests similar to the checkin and merge-to-master CI runs run:
```
cd $ALIGN_HOME
# Checkin
pytest -vv
CI_LEVEL='checkin' pytest -n 8 -s -vv --runnightly --maxerrors=1 --placer_sa_iterations 100 -- tests/integration/
# Merge to master
CI_LEVEL='merge' pytest -n 8 -s -vv --runnightly --maxerrors=20 --placer_sa_iterations 100 -- tests/integration/ tests/pdks
```

### Step 4: Run ALIGN
You may run the align tool using a simple command line tool named `schematic2layout.py`
For most common cases, you will simply run:
```console
$ schematic2layout.py <NETLIST_DIR> -p <PDK_DIR> -c
```

For instance, to build the layout for telescopic_ota:
```console
$ mkdir work && cd work
$ schematic2layout.py ../examples/telescopic_ota -p ../pdks/FinFET14nm_Mock_PDK/
```

For a full list of options supported by the tool, please use the following command:
```console
$ schematic2layout.py -h
```

## Design database:

* [examples](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples): Contains example circuits with netlists running on circleci
* [CircuitsDatabase](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/CircuitsDatabase): Contains benchmark circuits

## Viewer :

The final output GDS can be viewed using by importing in virtuoso or any GDS viewer
* [KLayout](https://github.com/KLayout/klayout): GDS viewer (WSL users would need to install xming for display to work)
* [Viewer](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/Viewer): Layout viewer to view output JSON file
