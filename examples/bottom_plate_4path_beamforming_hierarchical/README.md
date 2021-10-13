# Commandline

This will start the flow, skipping the routing, checking and GDS generation phases.
```
cd $ALIGN_WORK_DIR
cp -rf $ALIGN_HOME/examples/bottom_plate_4path_beamforming_hierarchical .
cd bottom_plate_4path_beamforming_hierarchical

schematic2layout.py dummy_design_dir -s bottom_plate_4path_beamforming_hierarchical  -p ../../pdks/Bulk65nm_Mock_PDK/ --gui --flow_start 3_pnr --flow_stop 3_pnr:route -n 1 --skipGDS --router_mode no_op
```
