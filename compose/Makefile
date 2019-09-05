# Makefile used to drive routing flow
#   ALIGN_HOME: top of hierarchy
#   ALIGN_WORK_DIR:  a working directory or a docker volume for running the flow

# To run in Docker: 
#   % make docker DESIGN=<design in $ALIGN_HOME/examples"

# To run natively:
#   % cd $ALIGN_WORK_DIR
#   % ln -sf $ALIGN_HOME/compose/Makefile $ALIGN_WORK_DIR
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
	export TOP = /
else
	execute = $(2)
	start =
	export TOP = ${ALIGN_HOME}
endif

# Convert output to PNG
${PNR_OUTPUT}/${DESIGN}_0.png:	${PNR_OUTPUT}/${DESIGN}_0.gds
	$(call execute, klayoutconvert-service, /bin/bash -c "cd $(TOP)/Build/ThirdParty/Klayout && ./gds2png.sh `pwd`/$< `pwd`/$@")

# Convert output to GDS
${PNR_OUTPUT}/${DESIGN}_0.gds:	${PNR_OUTPUT}/${DESIGN}_0.gds.json
	$(call execute,cellfabric-service, /bin/bash -c "source general/bin/activate && python3 $(TOP)/GDSConv/gdsconv/json2gds.py $< $@")

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
	$(call execute,cellfabric-service, /bin/bash -c "source general/bin/activate && mkdir -p ${GEN_OUTPUT} && cd \$$_ && make -f $(TOP)/CellFabric/Makefile INPUT=/`pwd`/${TPO_OUTPUT} DESIGN=${DESIGN}")

# Build the cell generator script
${TPO_OUTPUT}/${DESIGN}_lef.sh:	${DESIGN}/${DESIGN}.sp services
	$(call execute,topology-service,/bin/bash -c "source general/bin/activate  && mkdir -p ${TPO_OUTPUT} && cd \$$_/.. && make -f $(TOP)/sub_circuit_identification/Makefile INPUT=/`pwd`/${DESIGN} DESIGN=${DESIGN}")

${DESIGN}/${DESIGN}.sp:	${EXAMPLES}/${DESIGN}/${DESIGN}.sp  ${DESIGN}
	cp ${EXAMPLES}/${DESIGN}/* ${DESIGN}/

${DESIGN}/${PDK_FILE}:	${ALIGN_HOME}/${PDK_DIR}/${PDK_FILE}  ${DESIGN}
	cp $< ${DESIGN}/

${DESIGN}:
	mkdir ${DESIGN}

clean:
	rm -rf ${DESIGN}/*

#
# Docker-related targets
#

# Whether we are using a volume or a directory changes the docker-compose file
ifeq (/, $(findstring /, $(ALIGN_WORK_DIR)))
export VOL=dir-type
dir-type:
	echo $(ALIGN_WORK_DIR) > dir-type
	rm -f vol-type make-docker-service
else
export VOL=vol-type
vol-type:
	echo $(ALIGN_WORK_DIR) > vol-type
	rm -f dir-type make-docker-service
endif

docker-vol-type.yml:	${ALIGN_HOME}/compose/docker-vol-type.yml
	cp $< .

docker-dir-type.yml:	${ALIGN_HOME}/compose/docker-dir-type.yml
	cp $< .

docker-core.yml:	${ALIGN_HOME}/compose/docker-core.yml
	cp $< .

docker:	make-docker-service
	docker-compose exec make-docker-service bash -c "make -f /ALIGN-public/compose/Makefile DESIGN=${DESIGN}"

services:	transfer-service protobuf-service \
		protobuf-service cellfabric-service placeroute-service \
		topology-service klayoutconvert-service

transfer-service:	docker-compose.yml
	$(call start, $@)
	touch $@

protobuf-service:	docker-compose.yml
	$(call start, $@)
	touch $@

cellfabric-service:	docker-compose.yml
	$(call start, $@)
	touch $@

placeroute-service:	docker-compose.yml
	$(call start, $@)
	touch $@

topology-service:	docker-compose.yml
	$(call start, $@)
	touch $@

klayoutconvert-service:	docker-compose.yml
	$(call start, $@)
	touch $@

fullbuild-service:	docker-compose.yml
	$(call start, $@)
	touch $@

docker-compose.yml:	$(VOL) docker-core.yml docker-$(VOL).yml
	cat docker-core.yml docker-$(VOL).yml > $@

#Only respin the container
make-docker-service:	docker-compose.yml volume
	docker-compose -p compose up -d $@
	docker cp $< make_docker_cont:/dataVolume/
	docker cp volume make_docker_cont:/dataVolume/
	touch $@

.PHONY: check_volume
volume:	check_volume

# If volume name changes, bring down the containers and remove the redirect vol
# FAILURE mode: services are marked as up in volume, but are not up.
check_volume:
ifneq ($(shell cat volume),$(ALIGN_WORK_DIR))
ifneq (, $(wildcard ./docker-compose.yml))
		echo "Recreating containers with volume change to $(ALIGN_WORK_DIR)"
		rm -f make-docker-service
		docker-compose down
endif
	docker volume rm -f compose_redirectVolume
	rm -f make-docker-service
	echo $(ALIGN_WORK_DIR) > volume
endif

# Use this if compose/ area changes
force-make-docker-service:
	rm -f docker-compose.yml
	make docker-compose.yml
	docker-compose up -d --build make-docker-service
	touch make-docker-service

docker-clean: docker-compose.yml
	docker-compose  exec make-docker-service bash -c "rm -f docker-compose.yml"

docker-buildclean: docker-compose.yml
	docker-compose  exec make-docker-service bash -c "rm -rf $(DESIGN)"

docker-filesdown:
	rm -f *service volume vol-type dir-type

docker-down: docker-filesdown docker-compose.yml
	docker-compose down
	docker volume rm -f compose_redirectVolume
	rm -f docker-compose.yml

docker-fulldown: docker-filesdown docker-compose.yml
	docker-compose -p compose down --rmi all --remove-orphans
	docker volume rm -f compose_redirectVolume
	rm -f docker-compose.yml

