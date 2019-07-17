SHELL = bash
PC=python3
HOME = /home/kunal001/Desktop/research_work/full_flow/ALIGN-public
INPUT_DIR = $(HOME)/examples/telescopic_ota
DESIGN_NAME =telescopic_ota
#INPUT_DIR = $(HOME)/examples/switched_capacitor_filter
#DESIGN_NAME = switched_capacitor_filter
#INPUT_DIR = $(HOME)/../input/testcase_equlizer/
#DESIGN_NAME = sdc
PDK_DIR = ../ALIGN/PDK_Abstraction/FinFET7nm_Mock_PDK/
PDK_FILE = ASAP7_PDK_Abstraction.json
Cell_generator = ../ALIGN/PDK_Abstraction/Cell_Fabric_Interdigitated_7nm
CELL_PATH?= CellFabric/Viewer/INPUT/mydesign_dr_globalrouting.json
DEF_PATH = CellFabric/Viewer/INPUT/mydesign_dr_globalrouting.json

list:
	@echo make clean
	@echo make compile
	@echo make annotate
	@echo make create_cell
	@echo make PnR
	@echo make ALIGN
	@echo make ALIGN_docker
clean:
	@rm -rf ./sub_circuit_identification/input_circuit/*
	@rm -rf ./sub_circuit_identification/results/*
	@rm -rf $(Cell_generator)/*gds
	@rm -rf $(Cell_generator)/*gds.json
	@rm -rf $(Cell_generator)/*lef
compile:
	pip install --quiet -r sub_circuit_identification/requirements.txt
	cd PlaceRouteHierFlow/ && make clean && make LP_DIR=$(HOME)/lpsolve JSON=$(HOME)/json;
	pip install python-gdsii

clean_docker:
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
	
annotate_docker:
	cp $(INPUT_DIR)/$(DESIGN_NAME).sp ./sub_circuit_identification/input_circuit/
	cd sub_circuit_identification && docker build -f Dockerfile -t topology .
	if [ ! "$$(docker ps -a -f name=topology_container)" ]; then docker stop topology_container; fi
	if [ "$$(docker ps -aq -f status=exited -f name=topology_container)" ]; then docker rm topology_container; fi
	docker run --name topology_container --mount source=inputVol,target=/INPUT topology bash -c "source /sympy/bin/activate && cd /DEMO/ && ./runme.sh $(DESIGN_NAME) && cp -r ./results /INPUT"
	docker cp topology_container:/INPUT/results ./sub_circuit_identification/

annotate: 
	@echo '-----------------------------------------------------------------------'
	@echo '         ###    ##          ##########    ######## ###     ##'
	@echo '        ## ##   ##              ##       ##        ####    ##'
	@echo '       ##   ##  ##              ##      ##         ## ##   ##'
	@echo '      ##     ## ##              ##      ##  ###### ##  ##  ##'
	@echo '      ######### ##              ##      ##      ## ##   ## ##'
	@echo '      ##     ## ##              ##       ##     ## ##    ####'
	@echo '      ##     ## #########   ##########    ######## ##     ###'
	@echo '-----------------------------------------------------------------------'
	@echo '#'
	@echo '# Contributors: UMN , TAMU and INTEL'
	@echo '#'
	@echo '########################################################################'
	@echo Starting sub circuit annotation
	@echo ""
	@cp $(INPUT_DIR)/$(DESIGN_NAME).sp ./sub_circuit_identification/input_circuit/
	cd ./sub_circuit_identification/ && ./runme.sh $(DESIGN_NAME)
	@echo Sub circuit annotation finished successfully
	@echo Check logs at sub_circuit_identification/LOG
	@echo "#########################################"

create_cell_docker: 
	@if [ -a  "$(Cell_generator)/$(DESIGN_NAME).lef" ]; \
		then \
		rm $(Cell_generator)/$(DESIGN_NAME).lef; \
		fi
	cp ./sub_circuit_identification/results/$(DESIGN_NAME)_lef.sh ./$(Cell_generator)/ && \
	cd  $(Cell_generator) && source $(DESIGN_NAME)_lef.sh
	cat $(Cell_generator)/*lef > $(Cell_generator)/$(DESIGN_NAME).lef

create_cell:
	@echo Cell Generation
	@echo ""
	@echo Creating primitive cells for PnR
	@if [ -a  "$(Cell_generator)/$(DESIGN_NAME).lef" ]; \
		then \
		rm  $(Cell_generator)/$(DESIGN_NAME).lef; \
		fi
	@cp ./sub_circuit_identification/results/$(DESIGN_NAME)_lef.sh ./$(Cell_generator)/ && \
	cd  $(Cell_generator) && source $(DESIGN_NAME)_lef.sh > cell_geneation.log
	@cat  $(Cell_generator)/*lef >  $(Cell_generator)/$(DESIGN_NAME).lef
	@echo Cell generation finished successfully
	@echo Check logs at cell_geneation.log 
	@echo "#########################################"

create_PnR_data:
	@echo Starting Place and Route 
	@echo ""
	@if [ -d "./testcase_latest" ]; then \
		rm -rf testcase_latest; \
	fi
	@mkdir testcase_latest 
	@echo 'Copying all data to testcase_latest directory'
	@cp $(Cell_generator)/$(DESIGN_NAME).lef ./testcase_latest
	@cp ./sub_circuit_identification/results/$(DESIGN_NAME).v ./testcase_latest
	@cp $(PDK_DIR)/$(PDK_FILE) ./testcase_latest
	@cp $(INPUT_DIR)/*.const ./testcase_latest/
	@cp -r $(Cell_generator)/*gds* ./testcase_latest/
	@ls ./testcase_latest/*gds.json -l | awk -F'/' '{print $$(NF)}' | awk -F'.' '{print $$1, $$1".gds"}' > ./testcase_latest/$(DESIGN_NAME).map

PnR_docker: create_PnR_data
	if [ ! "$$(docker ps -a -f name=PnR)" ]; then docker stop PnR; fi
	if [ "$$(docker ps -aq -f status=exited -f name=PnR)" ]; then docker rm PnR; fi
	(cd testcase_latest; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"
	docker run --name PnR --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./tester ./INPUT $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME); mkdir results;cp $(DESIGN_NAME)* results/"
	docker cp PnR:/PlaceRouteHierFlow/results/ ./testcase_latest/

PnR:
	@echo ""
	@echo check logs at PlaceRouteHierFlow/PnR.log
	@cp -rp testcase_latest ./PlaceRouteHierFlow
	@if [ ! -d "./lpsolve" ]; then \
		git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git; \
	fi
	@if [ ! -d "./json" ]; then \
		git clone https://github.com/nlohmann/json.git; \
	fi
	@export LD_LIBRARY_PATH=$(HOME)/lpsolve/lp_solve_5.5.2.5_dev_ux64 && \
	cd PlaceRouteHierFlow/ && ./tester ./testcase_latest $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME) >  PnR.log
	@if [ ! -d "./testcase_latest/results" ]; then \
		mkdir ./testcase_latest/results; \
	fi
	@mv PlaceRouteHierFlow/$(DESIGN_NAME)* testcase_latest/results/
	@if [ ! -a "testcase_latest/results/$(DESIGN_NAME).gds" ]; then \
		echo PnR finished successfully; \
		echo "#########################################"; \
	fi
	@echo "Creating gds"
	@echo Check results at: testcase_latest/results/$(DESIGN_NAME).gds;
	@$(PC) ./testcase_latest/json2gds.py ./testcase_latest/results/$(DESIGN_NAME)_DR.gds.json ./testcase_latest/results/$(DESIGN_NAME).gds

view_result: 
ifneq (, $(shell which klayout))
	@klayout ./testcase_latest/results/$(DESIGN_NAME).gds &
endif
	
ALIGN_docker:build_docker annotate_docker create_cell_docker PnR_docker view_result
	echo "Done"
	

ALIGN:annotate create_cell create_PnR_data PnR

local_view_cell:
ifneq ($(CELL_PATH),$(DEF_PATH))
	cp -rf $(CELL_PATH) $(DEF_PATH)
endif
	cd $(Cell_generator)/Viewer/ && firefox index.html




