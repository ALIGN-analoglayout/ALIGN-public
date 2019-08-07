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

# Convert output to PNG
${PNR_OUTPUT}/${DESIGN}_0.png:	${PNR_OUTPUT}/${DESIGN}_0.gds
	docker-compose -p compose exec klayoutconvert-service /bin/bash -c "./gds2png.sh /dataVolume/$< /dataVolume/$@"

# Convert output to GDS
${PNR_OUTPUT}/${DESIGN}_0.gds:	${PNR_OUTPUT}/${DESIGN}_0.gds.json
	docker-compose -p compose  exec cellfabric-service /bin/bash -c "source general/bin/activate && cd /dataVolume/ && python3 /GDSConv/gdsconv/json2gds.py $< $@"

# Transfer inputs and run placeroute
${PNR_OUTPUT}/${DESIGN}_0.gds.json: ${GEN_OUTPUT}/${DESIGN}.lef ${TPO_OUTPUT}/${DESIGN}.v ${DESIGN}/${PDK_FILE}
	-docker-compose -p compose exec transfer-service bash -c "mkdir -p /dataVolume/${PNRDIR}/inputs && cd /dataVolume/${PNRDIR} && \
	cp /dataVolume/$(DESIGN)/$(PDK_FILE) inputs && \
	cp /dataVolume/$(GEN_OUTPUT)/$(DESIGN).lef inputs && \
	cp /dataVolume/$(GEN_OUTPUT)/$(DESIGN).map inputs && \
	cp /dataVolume/$(GEN_OUTPUT)/*.gds.json inputs && \
	cp /dataVolume/$(TPO_OUTPUT)/$(DESIGN).v inputs && \
	cp /dataVolume/$(TPO_OUTPUT)/*.const inputs"
	docker-compose -p compose  exec placeroute-service /bin/bash -c "cd /dataVolume && mkdir -p ${PNR_OUTPUT} && cd ${PNRDIR} && make -f /PlaceRouteHierFlow/Makefile.run DESIGN=${DESIGN} |& tee Results/PnR.log"

# Run the cell generator
${GEN_OUTPUT}/${DESIGN}.lef:	${TPO_OUTPUT}/${DESIGN}_lef.sh
	docker-compose -p compose  exec cellfabric-service /bin/bash -c "source /general/bin/activate && cd /dataVolume/ && mkdir -p ${GEN_OUTPUT} && cd ${GEN_OUTPUT} && make -f /CellFabric/Makefile INPUT=/dataVolume/${TPO_OUTPUT} DESIGN=${DESIGN}"

# Build the cell generator script
${TPO_OUTPUT}/${DESIGN}_lef.sh:	${DESIGN}/${DESIGN}.sp docker-compose.yml
	docker-compose -p compose  exec topology-service /bin/bash -c "source /sympy/bin/activate && cd /dataVolume/ && mkdir -p ${TPO_OUTPUT} && cd ${TPO_OUTPUT}/.. && make -f /DEMO/Makefile INPUT=/dataVolume/${DESIGN} DESIGN=${DESIGN}"

docker-compose.yml:	${ALIGN_HOME}/compose/docker-compose.yml
	ln -s $< $@
	docker-compose -p compose  up -d transfer-service
	docker-compose -p compose  up -d protobuf-service
	docker-compose -p compose  up -d cellfabric-service
	docker-compose -p compose  up -d placeroute-service
	docker-compose -p compose  up -d topology-service
	docker-compose -p compose  up -d klayoutconvert-service

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

