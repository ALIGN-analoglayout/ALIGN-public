SHELL = bash
PC=python3
HOME = $(PWD)
DESIGN_NAME = telescopic_ota
INPUT_DIR = $(HOME)/examples/$(DESIGN_NAME)
PDK_DIR = PDK_Abstraction/FinFET14nm_Mock_PDK/
PDK_FILE = FinFET_Mock_PDK_Abstraction.json
Cell_generator = CellFabric/Cell_Fabric_FinFET__Mock
CELL_PATH?= CellFabric/Viewer/larger_example/mydesign_dr_globalrouting.json
DEFAULT_PATH = CellFabric/Viewer/larger_example/mydesign_dr_globalrouting.json
.SILENT: list clean create_PnR_data
list:
	echo make clean
	echo make compile
	echo make annotate
	echo make create_cell
	echo make create_PnR_data
	echo make PnR
	echo make ALIGN
	echo make ALIGN_docker
clean:
	rm -rf ./sub_circuit_identification/input_circuit/*
	rm -rf ./sub_circuit_identification/library_graphs/*
	rm -rf ./sub_circuit_identification/circuit_graphs/*
	rm -rf ./sub_circuit_identification/results/*
	rm -rf $(Cell_generator)/*gds
	rm -rf $(Cell_generator)/*.json
	rm -rf $(Cell_generator)/*gds.json
	rm -rf $(Cell_generator)/*lef
	rm -rf PlaceRouteHierFlow/PnR.log
	rm -rf PlaceRouteHierFlow/testcase_latest
	rm -rf PlaceRouteHierFlow/Results
	rm -rf testcase_latest
compile:
	pip install --quiet -r sub_circuit_identification/requirements.txt
	@if [ ! -d "./lpsolve" ]; then \
		git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git; \
	fi
	@if [ ! -d "./json" ]; then \
		git clone https://github.com/nlohmann/json.git; \
	fi
	cd PlaceRouteHierFlow/ && make clean && make LP_DIR=$(HOME)/lpsolve JSON=$(HOME)/json;
	pip install python-gdsii
	cd GDSConv && pip install -e .
	cd CellFabric && pip install -e . && pytest

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
	if [ -d "./PlaceRouteHierFlow/Results" ]; then \
		rm -rf ./PlaceRouteHierFlow/Results; \
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
	@echo '         ###    ##        ##########    ######## ###     ##'
	@echo '        ## ##   ##            ##       ##        ####    ##'
	@echo '       ##   ##  ##            ##      ##         ## ##   ##'
	@echo '      ##     ## ##            ##      ##  ###### ##  ##  ##'
	@echo '      ######### ##            ##      ##      ## ##   ## ##'
	@echo '      ##     ## ##            ##       ##     ## ##    ####'
	@echo '      ##     ## ######### ##########    ######## ##     ###'
	@echo '-----------------------------------------------------------------------'
	@echo '#'
	@echo '# Contributors: UMN , TAMU and INTEL'
	@echo '#'
	@echo '########################################################################'
	@echo Starting sub circuit annotation
	@echo ""
	@cp $(INPUT_DIR)/$(DESIGN_NAME).sp ./sub_circuit_identification/input_circuit/
	@cp $(INPUT_DIR)/*.const ./sub_circuit_identification/input_circuit/
	cd ./sub_circuit_identification/ && time ./runme.sh $(DESIGN_NAME)
	@echo Sub circuit annotation finished successfully
	@echo Check logs at sub_circuit_identification/LOG
	@echo "#########################################"

create_cell_docker: 
	@echo Cell Generation
	@echo ""
	@echo Creating primitive cells for PnR
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
	cd  $(Cell_generator) && time source $(DESIGN_NAME)_lef.sh > cell_geneation.log
	@cat  $(Cell_generator)/*lef >  $(Cell_generator)/$(DESIGN_NAME).lef
	@echo Cell generation finished successfully
	@echo Check logs at cell_generation.log 
	@echo "#########################################"

create_PnR_data:
	echo Starting Place and Route 
	echo ""
	if [ -d "./testcase_latest" ]; then \
		rm -rf testcase_latest; \
	fi
	mkdir testcase_latest 
	echo 'Copying all data to testcase_latest directory'
	cp $(Cell_generator)/$(DESIGN_NAME).lef ./testcase_latest
	cp ./sub_circuit_identification/results/$(DESIGN_NAME).v ./testcase_latest
	cp $(PDK_DIR)/$(PDK_FILE) ./testcase_latest
	-cp $(INPUT_DIR)/*.const ./testcase_latest/
	-cp ./sub_circuit_identification/results/*.const ./testcase_latest/
	cp -r $(Cell_generator)/*gds* ./testcase_latest/
	ls ./testcase_latest/*gds.json -l | awk -F'/' '{print $$(NF)}' | awk -F'.' '{print $$1, $$1".gds"}' > ./testcase_latest/$(DESIGN_NAME).map

PnR_docker: create_PnR_data
	if [ ! "$$(docker ps -a -f name=PnR)" ]; then docker stop PnR; fi
	if [ "$$(docker ps -aq -f status=exited -f name=PnR)" ]; then docker rm PnR; fi
	(cd testcase_latest; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"
	docker run --name PnR --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./pnr_compiler ./INPUT $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME) 1 0| tee > PnR.log; "
	docker cp PnR:/PlaceRouteHierFlow/Results/ ./testcase_latest/
	@echo "Creating gds"
	@echo Check results at: testcase_latest/Results/$(DESIGN_NAME).gds;
	@$(PC) GDSConv/gdsconv/json2gds.py ./testcase_latest/Results/$(DESIGN_NAME)_0.gds.json ./testcase_latest/Results/$(DESIGN_NAME).gds

PnR:
	@echo ""
	@echo check logs at PlaceRouteHierFlow/PnR.log
	@cp -rp testcase_latest ./PlaceRouteHierFlow
	export LD_LIBRARY_PATH=$(HOME)/lpsolve/lp_solve_5.5.2.5_dev_ux64 && \
	cd PlaceRouteHierFlow/ && time ./pnr_compiler ./testcase_latest $(DESIGN_NAME).lef $(DESIGN_NAME).v $(DESIGN_NAME).map $(PDK_FILE) $(DESIGN_NAME) 1 0|tee > PnR.log 
	@if [ ! -d "./testcase_latest/Results" ]; then \
		mkdir ./testcase_latest/Results; \
	fi
	@cp -f PlaceRouteHierFlow/Results/$(DESIGN_NAME)* testcase_latest/Results/
	@if [ ! -a "testcase_latest/Results/$(DESIGN_NAME).gds" ]; then \
		echo PnR finished successfully; \
		echo "#########################################"; \
	fi
	@echo "Creating gds"
	@echo Check results at: testcase_latest/Results/$(DESIGN_NAME).gds;
	@$(PC) GDSConv/gdsconv/json2gds.py ./testcase_latest/Results/$(DESIGN_NAME)_0.gds.json ./testcase_latest/Results/$(DESIGN_NAME).gds

view_result: 
ifneq (, $(shell which klayout))
	@klayout ./testcase_latest/Results/$(DESIGN_NAME)_0.gds &
endif

ALIGN_docker:build_docker annotate_docker create_cell_docker PnR_docker view_result
	echo "Done"

ALIGN:annotate create_cell create_PnR_data PnR

local_view_cell:
ifneq ($(CELL_PATH),$(DEFAULT_PATH))
	cp -rf $(CELL_PATH) $(DEFAULT_PATH)
endif
	cd $(Cell_generator)/Viewer/ && firefox index.html




