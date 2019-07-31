[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/2aeb84c0f14949909bcd342b19721d01)](https://app.codacy.com/app/ALIGN-analoglayout/ALIGN-public?utm_source=github.com&utm_medium=referral&utm_content=ALIGN-analoglayout/ALIGN-public&utm_campaign=Badge_Grade_Settings)

 This the main repository for the DARPA IDEA ALIGN project led by University of Minnesota.

# Push Button Flow
 * make ALIGN : Runs the full flow using single command
 * make ALIGN_docker : Runs the full flow on Docker 
```bash
  - update local paths in Makefile before running the tool [line 1-7]
  - make : lists all available commands 
  - make compile : required once for setting up the tool
```

## (Proposed) Push Button Docker Flow
*  Works from a separate directory pointing to ALIGN_HOME, managing dependencies correctly, handles proxies, uses a single shared volume.
   *  make DESIGN=<example>
      1.  updates the docker images
      -   brings up running containers, ready to execute commands
      -   exec's commands in running containers 
   *  clean : removes files, shuts down containers.

# Design Flow 
## Continuous Integration
```bash
  - Circleci to integrate code from multiple developers. 
  - Each check-in is verified automatically.
  - Code coverage and quality checks are done before merging.
  - Cross platform using Docker.
```
## Design database:
 * Contains example circuits with netlist, schematic
 
## Build : 

* Docker setup initialization for c++/python


## Circuit Annotation :

* Sub_circuit_identification: Reading and annotating netlist
```bash
  - Generates a verilog file for input circuit. 
  - Generates input for parametric cell generator.
```
* Constraints: JSON format (manual)

## PDK abstraction: (Some parts are private)

* PDK_Abstraction: JSON file format
* CellFabric: Parametric cell generation
```bash
  - Creation of LEF and GDS for cells based on PDK data ( private github).
  - The sizing is parameterized based on sizing in input netlist.
```
## Placement and Routing : 
* PlaceRouteHierFlow: (private)
```bash
Hierarchical placement and router.
Final output is stored in gds format
```
* PlacemenEditor: 
```bash
  - View and edit placements of leaf cells. 
  - Shows bounding box of all wires while moving around a particular leaf.
```
* Cktgen: Intel detail router example
```bash
  - Takes leaf cell placement and global routing information and sets up the detailed routing task.
  - Run Intel’s detailed router. 
```
## Viewer :
* GDS output: KLayout: https://github.com/KLayout/klayout
* JSON output: Layout viewer from JSON file

## Tutorials: Not exhaustive (WIP)

## Miscellaneous 
```bash
PySat : 
  - SAT-based toolkit
  - SAT-based leaf cell placer
  - SAT-based global router 
  - Full design example for equalizer
```

