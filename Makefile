SHELL = bash
PC=python3
HOME = /home/kunal001/Desktop/research_work/full_flow/ALIGN-public
INPUT_DIR = $(HOME)/../input/OTA/FD_OTA_ASAP7nm/Netlist/
DESIGN_NAME = telescopic_ota
PDK_DIR = ./PDK_Abstraction/FinFET7nm_Mock_PDK/
PDK_FILE = ASAP7_PDK_Abstraction.json
Cell_generator = Cell_Fabric_Interdigitated_7nm
CELL_PATH?= $(Cell_generator)/Viewer/INPUT/mydesign_dr_globalrouting.json
DEF_PATH = $(Cell_generator)/Viewer/INPUT/mydesign_dr_globalrouting.json

#COMMAND =  $(shell source install.sh)
#.PHONY: work templates 

clean-docker:
	docker container prune
	docker image prune -a
	docker volume prune
	docker ps -a
	docker volume ls
	docker image ls

build_docker:  
	cd Build && docker build -f Dockerfile.build -t with_protobuf . 
	cd sub_circuit_identification && docker build -f Dockerfile -t topology .
	if [ -d "./PlaceRouteHierFlow/results" ]; then \
		rm -rf ./PlaceRouteHierFlow/results; \
	fi
	cd PlaceRouteHierFlow && docker build -f Dockerfile -t placeroute_image .
	
annotate:
	cp $(INPUT_DIR)/$(DESIGN_NAME).sp ./sub_circuit_identification/input_circuit/
	docker build -f sub_circuit_identification/Dockerfile -t topology .
	if [ ! "$$(docker ps -a -f name=topology_container)" ]; then docker stop topology_container; fi
	if [ "$$(docker ps -aq -f status=exited -f name=topology_container)" ]; then docker rm topology_container; fi
	docker run --name topology_container --mount source=inputVol,target=/INPUT topology bash -c "source /sympy/bin/activate && cd /DEMO/ && ./runme.sh $(DESIGN_NAME) && cp -r ./results /INPUT"
	docker cp topology_container:/INPUT/results ./sub_circuit_identification/

local_annotate: 
	cp $(INPUT_DIR)/$(DESIGN_NAME).sp ./sub_circuit_identification/input_circuit/
	cd ./sub_circuit_identification/ && ./runme.sh $(DESIGN_NAME)

create_cell: 
	if [ -a  "$(Cell_generator)/$(DESIGN_NAME).lef" ]; \
		then \
		rm $(Cell_generator)/$(DESIGN_NAME).lef; \
		fi
	cp ./sub_circuit_identification/results/$(DESIGN_NAME)_lef.sh ./$(Cell_generator)/ && \
	cd  $(Cell_generator) && source $(DESIGN_NAME)_lef.sh
	cat $(Cell_generator)/*lef > $(Cell_generator)/$(DESIGN_NAME).lef

local_create_cell:
	if [ -a  "$(Cell_generator)/$(DESIGN_NAME).lef" ]; \
		then \
		rm  $(Cell_generator)/$(DESIGN_NAME).lef; \
		fi
	pip install -r sub_circuit_identification/requirements.txt
	cp ./sub_circuit_identification/results/$(DESIGN_NAME)_lef.sh ./$(Cell_generator)/ && \
	cd  $(Cell_generator) && source $(DESIGN_NAME)_lef.sh
	cat  $(Cell_generator)/*lef >  $(Cell_generator)/$(DESIGN_NAME).lef

create_PnR_data:
	if [ -d "./testcase_latest" ]; then \
		rm -rf testcase_latest; \
	fi
	mkdir testcase_latest 
	cp $(Cell_generator)/$(DESIGN_NAME).lef ./testcase_latest/
	cp ./sub_circuit_identification/results/$(DESIGN_NAME).v ./testcase_latest/
	cp $(PDK_DIR)/$(PDK_FILE) ./testcase_latest/
	cp $(INPUT_DIR)/$(DESIGN_NAME).const ./testcase_latest/
	cp $(Cell_generator)/*gds* ./testcase_latest/
	ls ./testcase_latest/*gds -l | awk -F'/' '{print $$(NF)}' | awk -F'.' '{print $$1, $$_}' > ./testcase_latest/$(DESIGN_NAME).map

PnR: create_PnR_data
	if [ ! "$$(docker ps -a -f name=PnR)" ]; then docker stop PnR; fi
	if [ "$$(docker ps -aq -f status=exited -f name=PnR)" ]; then docker rm PnR; fi
	(cd testcase_latest; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"
	docker run --name PnR --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./tester ./INPUT $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME); mkdir results;cp $(DESIGN_NAME)* results/"
	docker cp PnR:/PlaceRouteHierFlow/results/ ./testcase_latest/

local_PnR: create_PnR_data
	cp -rp testcase_latest ./PlaceRouteHierFlow
	if [ ! -d "./lpsolve" ]; then \
		git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git; \
	fi
	if [ ! -d "./json" ]; then \
		git clone https://github.com/nlohmann/json.git; \
	fi
	cd PlaceRouteHierFlow/ && make clean && make LP_DIR=$(HOME)/lpsolve JSON=$(HOME)/json
	export LD_LIBRARY_PATH=$(HOME)/lpsolve/lp_solve_5.5.2.5_dev_ux64 && \
	cd PlaceRouteHierFlow/ && ./tester ./testcase_latest $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME)
	if [ ! -d "./testcase_latest/results" ]; then \
		mkdir ./testcase_latest/results; \
	fi
	mv PlaceRouteHierFlow/$(DESIGN_NAME)* testcase_latest/results/

view_result: 
	pip install python-gdsii
	$(PC) ./testcase_latest/json2gds.py ./testcase_latest/results/$(DESIGN_NAME)_DR.gds.json ./testcase_latest/results/$(DESIGN_NAME).gds
ifneq (, $(shell which klayout))
	klayout ./testcase_latest/results/$(DESIGN_NAME).gds
endif
	
ALIGN_all:build_docker annotate create_cell PnR view_result
	echo "Done"
	

ALIGN_local_all:local_annotate local_create_cell local_PnR view_result

local_view_cell:
ifneq ($(CELL_PATH),$(DEF_PATH))
	cp -rf $(CELL_PATH) $(DEF_PATH)
endif
	cd $(Cell_generator)/Viewer/ && firefox index.html




