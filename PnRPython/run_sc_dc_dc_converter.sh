#!/bin/bash

export DESIGN=sc_dc_dc_converter

./gen_viewer_json.py -b $DESIGN -o ../Viewer/INPUT -d $ALIGN_WORK_DIR/$DESIGN/pnr_output/Results -l INFO  --json_dir $ALIGN_WORK_DIR/$DESIGN/pnr_output/inputs/ --draw_grid
