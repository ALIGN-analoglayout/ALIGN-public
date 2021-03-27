# Makefile used to drive routing flow
#   ALIGN_HOME: top of hierarchy
#   ALIGN_WORK_DIR:  a working directory or a docker volume for running the flow

# To run in Docker: 
#   % make docker DESIGN=<design in $ALIGN_HOME/examples"

# To run natively:
#   % cd $ALIGN_WORK_DIR
#   % ln -sf $ALIGN_HOME/build/Makefile $ALIGN_WORK_DIR
#   % make DESIGN=<design in $ALIGN_HOME/examples"

VENV=/opt/venv

EXAMPLES=${ALIGN_HOME}/examples

DESIGN=telescopic_ota
PDK_DIR=pdks/FinFET14nm_Mock_PDK
PDK_FILE=layers.json
FLAT=0

OUTPUT_DIR=${DESIGN}

ifeq ($(BUILD),docker)
	execute = docker-compose -p build exec $(1) $(2)
	start = docker-compose -p build up -d $(1)
	export TOP = /
else
	execute = $(2)
	start =
	export TOP = ${ALIGN_HOME}
endif

# Convert schematic to gds & PNG
${OUTPUT_DIR}/${DESIGN}_0.png:	${EXAMPLES}/${DESIGN}/${DESIGN}.sp  ${DESIGN}
	$(call execute,align-service, /bin/bash -c "source ${ALIGN_HOME}/setup.sh && unset ALIGN_WORK_DIR && cd ${DESIGN} && schematic2layout.py ${EXAMPLES}/${DESIGN} -f ${EXAMPLES}/${DESIGN}/${DESIGN}.sp -s ${DESIGN} -p ${ALIGN_HOME}/${PDK_DIR} -flat ${FLAT} -c -g")

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

docker-vol-type.yml:	${ALIGN_HOME}/build/docker-vol-type.yml
	cp $< .

docker-dir-type.yml:	${ALIGN_HOME}/build/docker-dir-type.yml
	cp $< .

docker-core.yml:	${ALIGN_HOME}/build/docker-core.yml
	cp $< .

docker:	volume align-service ${DESIGN}
	docker-compose exec align-service bash -c "make -f /ALIGN-public/build/Makefile DESIGN=${DESIGN} FLAT=${FLAT}"
	docker cp align_container:/dataVolume/${OUTPUT_DIR}/${DESIGN}_0.png ./${DESIGN}/
	docker cp align_container:/dataVolume/${OUTPUT_DIR}/${DESIGN}_0.gds ./${DESIGN}/
	docker cp align_container:/dataVolume/${OUTPUT_DIR}/LOG ./${DESIGN}/

services:	transfer-service align-service \
		klayoutconvert-service

transfer-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

protobuf-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

align-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

placeroute-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

klayoutconvert-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

fullbuild-service:	docker-compose.yml
	docker-compose -p build up -d $@
	touch $@

docker-compose.yml:	$(VOL) docker-core.yml docker-$(VOL).yml volume
	cat docker-core.yml docker-$(VOL).yml > $@

# Only respin the container
make-docker-service:	docker-compose.yml 
	echo "Here newer $?"
	docker-compose -p build up -d $@
	docker cp volume make_docker_cont:/dataVolume/
	docker cp docker-compose.yml make_docker_cont:/dataVolume/
	touch $@

.PHONY: check_volume
volume:	check_volume

# If volume name changes, bring down the containers and remove the redirect vol
# FAILURE mode: services are marked as up in volume, but are not up -- fix is volume entries above
check_volume:
ifneq ($(shell cat volume),$(ALIGN_WORK_DIR))
ifneq (, $(wildcard ./docker-compose.yml))
		-echo "Recreating containers with volume change to $(ALIGN_WORK_DIR)"
		rm -f *-service
		docker-compose down
endif
	docker volume rm -f compose_redirectVolume
	rm -f make-docker-service
	echo $(ALIGN_WORK_DIR) > volume
endif

# Use this if build/ area changes
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
	docker-compose -p build down --rmi all --remove-orphans
	docker volume rm -f compose_redirectVolume
	rm -f docker-compose.yml

