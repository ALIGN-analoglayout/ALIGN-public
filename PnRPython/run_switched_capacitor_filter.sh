#!/bin/bash

export DESIGN=switched_capacitor_filter

for blk in telescopic_ota switched_capacitor_combination $DESIGN; do
./gen_viewer_json.py -b $blk -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --check

./gen_viewer_json.py -b $blk -o ../Viewer/INPUT -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --draw_grid

done
