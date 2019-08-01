# Makefile which uses docker-compose

#export ALIGN_HOME=~/src/ALIGN-public/

EXAMPLES=${ALIGN_HOME}/examples

DESIGN=telescopic_ota
PDK_DIR=PDK_Abstraction/FinFET14nm_Mock_PDK/
PDK_FILE=FinFET_Mock_PDK_Abstraction.json
CELL_GENERATOR=CellFabric/Cell_Fabric_FinFET__Mock

PNR_OUTPUT=${DESIGN}/pnr_output/Results
GEN_OUTPUT=${DESIGN}/generator_output
TPO_OUTPUT=${DESIGN}/topology_output/Results

# Convert output to PNG
${PNR_OUTPUT}/${DESIGN}_0.png:	${PNR_OUTPUT}/${DESIGN}_0.gds
	docker-compose exec klayoutconvert-service /bin/bash -c "./gds2png.sh /dataVolume/$< /dataVolume/$@"

# Convert output to GDS
${PNR_OUTPUT}/${DESIGN}_0.gds:	${PNR_OUTPUT}/${DESIGN}_0.gds.json
	docker-compose exec cellfabric-service /bin/bash -c "source general/bin/activate && cd /dataVolume/ && python3 /GDSConv/gdsconv/json2gds.py $< $@"

${PNR_OUTPUT}/${DESIGN}_0.gds.json: ${GEN_OUTPUT}/${DESIGN}.lef ${TPO_OUTPUT}/${DESIGN}.v ${DESIGN}/${PDK_FILE}
	docker-compose exec placeroute-service /bin/bash -c "cd /dataVolume && mkdir -p ${PNR_OUTPUT} && cd ${PNR_OUTPUT}/.. && make -f /PlaceRouteHierFlow/Makefile.run DESIGN=${DESIGN} LAYINPUT=/dataVolume/${GEN_OUTPUT} NETINPUT=/dataVolume/${TPO_OUTPUT} PDKINPUT=/dataVolume/${DESIGN} |& tee Results/PnR.log"

${GEN_OUTPUT}/${DESIGN}.lef:	${TPO_OUTPUT}/${DESIGN}_lef.sh
	docker-compose exec cellfabric-service /bin/bash -c "source /general/bin/activate && cd /dataVolume/ && mkdir -p ${GEN_OUTPUT} && cd ${GEN_OUTPUT} && make -f /CellFabric/Makefile INPUT=/dataVolume/${TPO_OUTPUT} DESIGN=${DESIGN}"

${TPO_OUTPUT}/${DESIGN}_lef.sh:	${DESIGN}/${DESIGN}.sp docker-compose.yml
	docker-compose exec topology-service /bin/bash -c "source /sympy/bin/activate && cd /dataVolume/ && mkdir -p ${TPO_OUTPUT} && cd ${TPO_OUTPUT}/.. && make -f /DEMO/Makefile INPUT=/dataVolume/${DESIGN} DESIGN=${DESIGN}"

docker-compose.yml:	${ALIGN_HOME}/compose/docker-compose.yml
	ln -s $< $@
	docker-compose up -d

${DESIGN}/${DESIGN}.sp:	${EXAMPLES}/${DESIGN}/${DESIGN}.sp  ${DESIGN}
	cp ${EXAMPLES}/${DESIGN}/`basename $< .sp`.* ${DESIGN}/

${DESIGN}/${DESIGN}.const:	${EXAMPLES}/${DESIGN}/${DESIGN}.const  ${DESIGN}
	cp $< ${DESIGN}/

${DESIGN}/${PDK_FILE}:	${ALIGN_HOME}/${PDK_DIR}/${PDK_FILE}  ${DESIGN}
	cp $< ${DESIGN}/

${DESIGN}:
	mkdir ${DESIGN}


clean:
	rm -rf ${DESIGN}/*

realclean:	clean
	docker-compose down
	rm docker-compose.yml

superclean:	clean
	docker-compose down --rmi all --remove-orphans
	rm docker-compose.yml

