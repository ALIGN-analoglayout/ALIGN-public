#!/bin/bash

export DESIGN=cascode_current_mirror_ota

for blk in CASCODED_CMC_NMOS CASCODED_CMC_PMOS $DESIGN; do
./gen_viewer_json.py -b $blk -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --check
done

./gen_viewer_json.py -b $DESIGN -o ../Viewer/INPUT -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --check

./gen_viewer_json.py -b $DESIGN -o ../Viewer/INPUT -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --draw_grid
