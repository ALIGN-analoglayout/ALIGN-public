#

#library_graphs:	basic_library/
#	python3 ./src/read_library.py --dir basic_library

INPUT=/dataVolume/topology_input
SRC=/DEMO/src

Results/${DESIGN}_lef.sh:

library_graphs:	/DEMO/basic_library
	python3 $(SRC)/read_library.py --dir /DEMO/basic_library

circuit_graphs/${DESIGN}.yaml: ${INPUT}/${DESIGN}.sp library_graphs
	python3 $(SRC)/read_netlist.py --dir ${INPUT} -f `basename $< .sp`.sp --subckt ${DESIGN} --flat 0

Results/${DESIGN}.p:	circuit_graphs/${DESIGN}.yaml
	python3 $(SRC)/match_graph.py

Results/${DESIGN}_lef.sh:	Results/${DESIGN}.p LEF
	python3 $(SRC)/write_verilog_lef.py -U_cap 12 -U_mos 12
	python3 $(SRC)/check_const.py --name ${DESIGN}

LEF:	/DEMO/LEF
	cp -r /DEMO/LEF .

clean:
	rm -rf circuit_graphs/${DESIGN}.yaml
	rm -rf Results/${DESIGN}.{p,v,_lef.sh}
