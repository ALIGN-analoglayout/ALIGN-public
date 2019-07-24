#!/bin/bash
if [ $# -eq 0 ]; then
    echo "please provide a design name"
    exit 1
else
    echo "Start annotating DESIGN Name : $1"
    DESIGN=$1
fi
# cleaning all files
rm -rf ./circuit_graphs/* LOG/* ./Results/*.p library_graphs/* 
## READ LIBRARY 
## Reads inputs netlist of spice format (".sp") from basic_library folder
## There is basic template of libraries which we provide: basic_template.sp
## User can add more templates in : user_template.sp
python3 ./src/read_library.py --dir basic_library
# the output is stored in library_graph in yaml format

## READ input netlist 
## Reads inputs netlist of spice format (".sp") from input_circuit folder
## User need to keep his spice netlist in this directory : switched_cap_filter.sp
SPICE_FILE="$DESIGN.sp"
python3 ./src/read_netlist.py --dir input_circuit -f $SPICE_FILE --subckt $DESIGN --flat 0
# the output is stored in circuit_graph directory in yaml format

## MATCH GRAPH
## loads graph from circuit_graph and matches the graphs defined in library_graph
## reduces the graph by merging nodes of matched graphs
python3 ./src/match_graph.py
#store the matches and reduced graph in pickle binary format 

python3 ./src/write_verilog_lef.py -U_cap 12 -U_mos 12
#store output in verilog format in results dir

#python ./src/write_constraints.py
## CHecks for common centroid constraint
python3 ./src/check_const.py
