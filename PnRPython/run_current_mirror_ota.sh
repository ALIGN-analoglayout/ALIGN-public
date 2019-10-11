#!/bin/bash

export DESIGN=current_mirror_ota

for blk in $DESIGN; do
./gen_viewer_json.py -b $blk -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --check
done

./gen_viewer_json.py -b $DESIGN -o ../Viewer/INPUT -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --draw_grid
