#!/bin/bash

##Step1: ## READ LIBRARY 
         ## Reads inputs netlist of spice format (".sp") from basic_library folder 
         ## There is basic template of libraries which we provide: basic_template.sp
         ## User can add more templates in : user_template.sp
         ## OUTPUT: The output is stored in library_graph in yaml format

python ./src/read_library.py

echo "The output is stored in library_graph in yaml format"

echo "Please enter to continue"

read inputvar

##Step2: ## READ input netlist 
         ## Reads inputs netlist of spice format (".sp") from input_circuit folder
         ## User need to keep his spice netlist in this directory : switched_cap_filter.sp
         ## OUTPUT: The output is stored in circuit_graph directory in yaml format

python ./src/read_netlist.py

echo "Reading input netlist successful"
echo "The output is stored in circuit_graph directory in yaml format"

echo "Please enter to continue"
read inputvar1
##Step3: ## MATCH GRAPH
         ## loads graph from circuit_graph and matches the graphs defined in library_graph
         ## Reduces the graph by merging nodes of matched graphs
         ## OUTPUT: Store the matches and reduced graph in pickle binary format 

python ./src/match_graph.py

##Step4: ## GENERATE VERILOG
       ## OUTPUT: Store output in verilog format in results dir

python ./src/write_verilog.py 

echo "The output is stored in results directory in verilog format"

echo "Please enter to continue"
read inputvar1
##Step5: Display the VERILOG file on terminal

python ./src/output.py 

