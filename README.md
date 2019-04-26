[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/2aeb84c0f14949909bcd342b19721d01)](https://app.codacy.com/app/ALIGN-analoglayout/ALIGN-public?utm_source=github.com&utm_medium=referral&utm_content=ALIGN-analoglayout/ALIGN-public&utm_campaign=Badge_Grade_Settings)

 This the main repository for the DARPA IDEA ALIGN project led by University of Minnesota.
 

# Design Flow 
Continuous Integration (CI) using circleci
## Design database:
## Build : 

* Docker setup initialization for c++/python
* Code coverage check setup example


## Circuit Annotation :

* Sub_circuit_identification: Reading and annotating netlist
```bash
Generates a verilog file for input circuit
Generates input for parametric cell generator
```
* Constraints: JSON format (manual)

## PDK abstraction: (Some parts are private)

* PDK_Abstraction: JSON file format
* Cell fabric: Parametric cell generation
```bash
Creation of LEF and GDS for cells based on PDK data ( private github)
```
## Placement and Routing :  
* PlacemenEditor: 
```bash
View and edit placements of leaf cells. Shows bounding box of all wires while moving around a particular leaf.
```
* Cktgen: Intel detail router example
```bash
Setup and run Intel’s detailed router. 
Takes leaf cell placement and global routing information and setups up the detailed routing task.
```
## Viewer :
* GDS output: KLayout: https://github.com/KLayout/klayout
* JSON output: Layout viewer from JSON file

## Tutorials: Not exhaustive (WIP)

## Miscellaneous 
```bash
PySat : 
SAT-based toolkit
SAT-based leaf cell placer
SAT-based global router 
Full design example for equalizer
```

