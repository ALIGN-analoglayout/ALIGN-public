#

INPUT=/dataVolume/topology_output/Results

LOC_GENERATOR=FinFET14nm_Mock_PDK
CELL_GENERATOR=/PDK_Abstraction/$(LOC_GENERATOR)
# Run the generator script

${DESIGN}.map:	${DESIGN}.lef
	ls *.gds.json -l | awk '{print $$NF}' | awk -F'.' '{print $$1,$$1".gds"}' > ${DESIGN}.map

${DESIGN}.lef:	${INPUT}/${DESIGN}_lef.sh  ../PDK_Abstraction $(LOC_GENERATOR)
	chmod u+x $<
	(cd ${LOC_GENERATOR}; rm -f *.lef; $< python3; cat *.lef > ${DESIGN}.lef)
	mv ${LOC_GENERATOR}/${DESIGN}.lef .
	mv ${LOC_GENERATOR}/*.json .

../PDK_Abstraction:	$(TOP)/PDK_Abstraction
	ln -s $< $@

$(LOC_GENERATOR):	$(TOP)/$(CELL_GENERATOR)
	cp -r $< .

