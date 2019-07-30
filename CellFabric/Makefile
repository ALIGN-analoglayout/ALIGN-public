#

INPUT=/dataVolume/topology_output/Results

LOC_GENERATOR=Cell_Fabric_FinFET__Mock
CELL_GENERATOR=/CellFabric/$(LOC_GENERATOR)
# Run the generator script

${DESIGN}.map:	${DESIGN}.lef
	ls *.gds.json -l | awk '{print $$NF}' | awk -F'.' '{print $$1,$$1".gds"}' > ${DESIGN}.map

${DESIGN}.lef:	${INPUT}/${DESIGN}_lef.sh  ../PDK_Abstraction $(LOC_GENERATOR)
	chmod u+x $<
	(cd ${LOC_GENERATOR}; $< python3; cat *.lef > ${DESIGN}.lef)
	mv ${LOC_GENERATOR}/${DESIGN}.lef .
	mv ${LOC_GENERATOR}/*gds.json .

../PDK_Abstraction:	/PDK_Abstraction
	ln -s $< $@

$(LOC_GENERATOR):	$(CELL_GENERATOR)
	cp -r $< .

