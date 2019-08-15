# Makefile used to drive routing flow
#   ALIGN_HOME: top of hierarchy
#   ALIGN_WORK_DIR:  a working directory or a docker volume for running the flow

# TO RUN: 
#   ln -sf $ALIGN_HOME/compose/Makefile $ALIGN_WORK_DIR
#   cd $ALIGN_WORK_DIR
#   % make DESIGN=<design in $ALIGN_HOME/examples"

EXAMPLES=${ALIGN_HOME}/examples

DESIGN=telescopic_ota
PDK_DIR=PDK_Abstraction/FinFET14nm_Mock_PDK/
PDK_FILE=FinFET_Mock_PDK_Abstraction.json
CELL_GENERATOR=CellFabric/Cell_Fabric_FinFET__Mock

PNRDIR=${DESIGN}/pnr_output/
PNR_OUTPUT=${DESIGN}/pnr_output/Results
GEN_OUTPUT=${DESIGN}/generator_output
TPO_OUTPUT=${DESIGN}/topology_output/Results

ifeq ($(BUILD),docker)
	execute = docker-compose -p compose exec $(1) $(2)
	start = docker-compose -p compose up -d $(1)
	TOP = /
else
	execute = $(2)
	start =
endif

# Convert output to PNG
${PNR_OUTPUT}/${DESIGN}_0.png:	${PNR_OUTPUT}/${DESIGN}_0.gds
	$(call execute, klayoutconvert-service, /bin/bash -c "cd $(TOP)/Build/ThirdParty/Klayout && ./gds2png.sh `pwd`/$< `pwd`/$@")

# Convert output to GDS
${PNR_OUTPUT}/${DESIGN}_0.gds:	${PNR_OUTPUT}/${DESIGN}_0.gds.json
	$(call execute,cellfabric-service, /bin/bash -c "source /general/bin/activate && python3 $(TOP)/GDSConv/gdsconv/json2gds.py $< $@")

# Transfer inputs and run placeroute
${PNR_OUTPUT}/${DESIGN}_0.gds.json: ${GEN_OUTPUT}/${DESIGN}.lef ${TPO_OUTPUT}/${DESIGN}.v ${DESIGN}/${PDK_FILE}
	-$(call execute, transfer-service, /bin/bash -c "mkdir -p ${PNRDIR}/inputs && \
	cp $(DESIGN)/$(PDK_FILE) \$$_ && \
	cp $(GEN_OUTPUT)/$(DESIGN).lef \$$_ && \
	cp $(GEN_OUTPUT)/$(DESIGN).map \$$_ && \
	cp $(GEN_OUTPUT)/*.gds.json \$$_ && \
	cp $(TPO_OUTPUT)/$(DESIGN).v \$$_ && \
	cp $(TPO_OUTPUT)/*.const \$$_")
	$(call execute, placeroute-service, /bin/bash -c "mkdir -p ${PNR_OUTPUT} && cd \$$_/.. && make -f $(TOP)/PlaceRouteHierFlow/Makefile.run DESIGN=${DESIGN} |& tee Results/PnR.log")

# Run the cell generator
${GEN_OUTPUT}/${DESIGN}.lef:	${TPO_OUTPUT}/${DESIGN}_lef.sh
	$(call execute,cellfabric-service, /bin/bash -c "source /general/bin/activate && mkdir -p ${GEN_OUTPUT} && cd \$$_ && make -f $(TOP)/CellFabric/Makefile INPUT=/`pwd`/${TPO_OUTPUT} DESIGN=${DESIGN}")

# Build the cell generator script
${TPO_OUTPUT}/${DESIGN}_lef.sh:	${DESIGN}/${DESIGN}.sp docker-compose.yml
	$(call execute,topology-service,/bin/bash -c "source /general/bin/activate  && mkdir -p ${TPO_OUTPUT} && cd \$$_/.. && make -f $(TOP)/sub_circuit_identification/Makefile INPUT=/`pwd`/${DESIGN} DESIGN=${DESIGN}")

docker-compose.yml:	${ALIGN_HOME}/compose/docker-compose.yml
	ln -s $< $@
	$(call start, transfer-service)
	$(call start, protobuf-service)
	$(call start, cellfabric-service)
	$(call start, placeroute-service)
	$(call start, topology-service)
	$(call start, klayoutconvert-service)

${DESIGN}/${DESIGN}.sp:	${EXAMPLES}/${DESIGN}/${DESIGN}.sp  ${DESIGN}
	cp ${EXAMPLES}/${DESIGN}/* ${DESIGN}/

${DESIGN}/${PDK_FILE}:	${ALIGN_HOME}/${PDK_DIR}/${PDK_FILE}  ${DESIGN}
	cp $< ${DESIGN}/

${DESIGN}:
	mkdir ${DESIGN}

clean:
	rm -rf ${DESIGN}/*

realclean:	clean
	docker-compose -p compose down
	rm docker-compose.yml

superclean:	clean
	docker-compose -p compose down --rmi all --remove-orphans
	rm docker-compose.yml

