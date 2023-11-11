# To run flow till placement step
```
schematic2layout.py -p ${ALIGN_HOME}/pdks/FinFET14nm_Mock_PDK/ ${ALIGN_HOME}/examples/fixed_height/ -b ${ALIGN_HOME}/examples/fixed_height/gdsfiles/ --router_mode no_op --place_using_ILP
```

# Generate GDS with the just the placement
```
gen_pl_gds.py -p 3_pnr/Results/FIXED_HEIGHT_0.scaled_placement_verilog.json -g ${ALIGN_HOME}/examples/fixed_height/gdsfiles -t FIXED_HEIGHT_0
```
