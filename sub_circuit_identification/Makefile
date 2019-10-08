#
INPUT=/dataVolume/$(DESIGN)

SRC=$(TOP)/sub_circuit_identification/src

Results/${DESIGN}_lef.sh:

library_graphs:	$(TOP)/sub_circuit_identification/basic_library
	python3 $(SRC)/read_library.py --dir $(TOP)/sub_circuit_identification/basic_library

circuit_graphs/${DESIGN}.yaml: input_circuit/${DESIGN}.sp library_graphs
	python3 $(SRC)/read_netlist.py --dir ./input_circuit -f `basename $< .sp`.sp --subckt ${DESIGN} --flat $(FLAT)

Results/${DESIGN}.p:	circuit_graphs/${DESIGN}.yaml
	python3 $(SRC)/match_graph.py

Results/${DESIGN}_lef.sh:	Results/${DESIGN}.p LEF
	python3 $(SRC)/write_verilog_lef.py -U_cap 12 -U_mos 12
	python3 $(SRC)/check_const.py --name ${DESIGN}

input_circuit/${DESIGN}.sp:	${INPUT}/${DESIGN}.sp
	mkdir -p ./input_circuit
	cp $< $@
	-cp -p ${INPUT}/*.const ./input_circuit/

LEF:	$(TOP)/sub_circuit_identification/LEF
	ls -ltr $(INPUT)
	cp -r $(TOP)/sub_circuit_identification/LEF .

clean:
	rm -rf circuit_graphs/${DESIGN}.yaml
	rm -rf Results/${DESIGN}{.p,.v,_lef.sh}
