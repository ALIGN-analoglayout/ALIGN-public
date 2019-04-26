[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/2aeb84c0f14949909bcd342b19721d01)](https://app.codacy.com/app/ALIGN-analoglayout/ALIGN-public?utm_source=github.com&utm_medium=referral&utm_content=ALIGN-analoglayout/ALIGN-public&utm_campaign=Badge_Grade_Settings)

 This the main repository for the DARPA IDEA ALIGN project led by University of Minnesota.
 
 Look in the *Build* subdirectory for build environments.

The Cktgen directory includes an example flow (placed primitives, global routing, detailed routing, and layout visualization.)

A sample process technology is included as well.

# Design Flow 
Continuous Integration (CI) using circleci
## Design database:
## Build : 
```bash
Docker setup initialization for c++/python
Code coverage check setup example
```

## Sub_circuit_identification :
```bash
Reading and annotating netlist
Creates a verilog file and a parametric lef generator
Constraints: manual 
JSON template 
```

## PDK abstraction: (Some parts are private)
```bash
 JSON file 
Cell fabric: 
Creation of LEF and GDS for cells based on PDK data ( private github)
```
## PlacementEditor:  
```bash
View and edit placements of leaf cells. Shows bounding box of all wires while moving around a particular leaf.
Cktgen: Intel detail router example
Setup and run Intel’s detailed router. Takes leaf cell placement and global routing information and setups up the detailed routing task.
```
## Viewer : 
GDS viewer KLayout: https://github.com/KLayout/klayout
Final results from JSON file
## Tutorials: Not exhaustive (WIP)

## Miscellaneous 
```bash
PySat : 

SAT-based toolkit

SAT-based leaf cell placer

SAT-based global router 

Full design example for equalizer
```

