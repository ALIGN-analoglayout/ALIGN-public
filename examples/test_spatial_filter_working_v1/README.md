 # Instructions for entrypoint 2 (subject to change)
 
 You need to create all the collateral normally construced by 1_topology and 2_primitives. For this testcase these files are:
 ```
./1_topology:
total 20
-rw-rw-r-- 1 smburns smburns 16167 May 24 09:39 bottom_plate_4path_beamforming.verilog.json
-rw-rw-r-- 1 smburns smburns   494 May 24 09:26 __primitives__.json

./2_primitives:
total 20
-rw-rw-r-- 1 smburns smburns  601 May 24 09:37 CAP_MIM_wt32_lt32.lef
-rw-rw-r-- 1 smburns smburns  470 May 24 09:37 RES_w1u_l14u.lef
-rw-rw-r-- 1 smburns smburns 1851 May 24 09:37 SW_NMOS_wr2u_lr60n_nr16.lef
-rw-rw-r-- 1 smburns smburns 5234 May 24 09:37 TIA_1.lef
```

For external lef files, the `__primitives__.json` file can be just a mapping between abstract and concrete names:
```
cat 1
{
  "RES_w1u_l14u": {
    "abstract_template_name": "RES_w1u_l14u",
    "concrete_template_name": "RES_w1u_l14u"
  },
  "CAP_MIM_wt32_lt32": {
    "abstract_template_name": "CAP_MIM_wt32_lt32",
    "concrete_template_name": "CAP_MIM_wt32_lt32"
  },
  "TIA_1": {
    "abstract_template_name": "TIA_1",
    "concrete_template_name": "TIA_1"
  },
  "SW_NMOS_wr2u_lr60n_nr16": {
    "abstract_template_name": "SW_NMOS_wr2u_lr60n_nr16",
    "concrete_template_name": "SW_NMOS_wr2u_lr60n_nr16"
  }
}
```
For generating placements and routings, the lef files are sufficient.
If you want to perform DRC and LVS checking of the result, you'll need the layout json files as well. If you want to generate GDS files, you'll need those too.

# Commandline

This will start the flow, skipping the checking and GDS generation phases.
```
cd $ALIGN_WORK_DIR
cp -rf $ALIGN_HOME/examples/test_spacial_filter_working_v1 .
cd test_spacial_filter_working_v1

schematic2layout.py dummy_design_dir -s bottom_plate_4path_beamforming  -p ../../pdks/Bulk65nm_Mock_PDK/ --gui --flow_start 3_pnr --flow_stop 3_pnr:route -n 40 --skipGDS
```

If you want to perform checking you need to generated the layout json files.
You can do this by running the `convert_lef_to_layout_json.py` script on each file that needs to be converted.
```
cd $ALIGN_WORK_DIR/test_spacial_filter_working_v1/2_primitives
convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n CAP_MIM_wt32_lt32
convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n RES_w1u_l14u
convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n TIA_1
convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n SW_NMOS_wr2u_lr60n_nr16
```

It is currently producing several warning messages about precision loss and off-grid pins.
```
(.venv) convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n CAP_MIM_wt32_lt32
align.cell_fabric.lef_to_json WARNING : bbox width not on grid 44240 40
(.venv) convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n RES_w1u_l14u
align.cell_fabric.lef_to_json WARNING : M1 pin PLUS not on grid 160 160
align.cell_fabric.lef_to_json WARNING : M1 pin MINUS not on grid 14380 80
align.cell_fabric.lef_to_json WARNING : bbox height not on grid 1300 100
align.cell_fabric.lef_to_json WARNING : bbox width not on grid 14540 240
(.venv) convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n TIA_1
align.cell_fabric.lef_to_json WARNING : M2 pin OUT_P not on grid 43580 180
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_P not on grid 9835 215
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_P not on grid 11745 45
align.cell_fabric.lef_to_json WARNING : M2 pin OUT_P not on grid 42240 40
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_P not on grid 3360 240
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_P not on grid 10080 200
align.cell_fabric.lef_to_json WARNING : M2 pin OUT_M not on grid 43580 180
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_M not on grid 31825 105
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_M not on grid 30295 135
align.cell_fabric.lef_to_json WARNING : M2 pin OUT_M not on grid 42240 40
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_M not on grid 26880 100
align.cell_fabric.lef_to_json WARNING : M1 pin OUT_M not on grid 28560 220
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 15767 167
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 26272 12
align.cell_fabric.lef_to_json WARNING : Rounding removes precision 39275.5 39276
align.cell_fabric.lef_to_json WARNING : Rounding removes precision 39564.5 39564
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 1680 120
align.cell_fabric.lef_to_json WARNING : Rounding removes precision 1535.5 1536
align.cell_fabric.lef_to_json WARNING : Rounding removes precision 1824.5 1824
align.cell_fabric.lef_to_json WARNING : M2 pin VDDA not on grid 39360 160
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 1680 120
align.cell_fabric.lef_to_json WARNING : M2 pin VDDA not on grid 18240 40
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 15960 100
align.cell_fabric.lef_to_json WARNING : M2 pin VDDA not on grid 18240 40
align.cell_fabric.lef_to_json WARNING : M1 pin VDDA not on grid 26040 40
align.cell_fabric.lef_to_json WARNING : M2 pin IN_M not on grid 24900 100
align.cell_fabric.lef_to_json WARNING : M2 pin IN_M not on grid 17080 80
align.cell_fabric.lef_to_json WARNING : M2 pin IN_M not on grid 24960 160
align.cell_fabric.lef_to_json WARNING : M1 pin IN_M not on grid 11760 60
align.cell_fabric.lef_to_json WARNING : M2 pin IN_M not on grid 17280 80
align.cell_fabric.lef_to_json WARNING : M2 pin IN_P not on grid 24900 100
align.cell_fabric.lef_to_json WARNING : M2 pin IN_P not on grid 17080 80
align.cell_fabric.lef_to_json WARNING : M2 pin IN_P not on grid 24960 160
align.cell_fabric.lef_to_json WARNING : M1 pin IN_P not on grid 28560 220
align.cell_fabric.lef_to_json WARNING : M2 pin IN_P not on grid 17280 80
align.cell_fabric.lef_to_json WARNING : M2 pin VSSA not on grid 3557 157
align.cell_fabric.lef_to_json WARNING : bbox height not on grid 48585 185
align.cell_fabric.lef_to_json WARNING : bbox width not on grid 23735 75
(.venv) convert_lef_to_layout_json.py -p $ALIGN_HOME/pdks/Bulk65nm_Mock_PDK/ -n SW_NMOS_wr2u_lr60n_nr16
align.cell_fabric.lef_to_json WARNING : M1 pin G not on grid 8110 50
align.cell_fabric.lef_to_json WARNING : M2 pin D not on grid 5890 90
align.cell_fabric.lef_to_json WARNING : M1 pin DNWP not on grid 8865 25
align.cell_fabric.lef_to_json WARNING : bbox height not on grid 7540 140
align.cell_fabric.lef_to_json WARNING : bbox width not on grid 8970 130
```

Now we can try to get the checking performed as well:
```
cd $ALIGN_WORK_DIR/test_spacial_filter_working_v1

schematic2layout.py dummy_design_dir -s bottom_plate_4path_beamforming  -p ../../pdks/Bulk65nm_Mock_PDK/ --gui --flow_start 3_pnr -n 40 --skipGDS
```

The run goes through with a bunch of off grid errors and opens because of the bad input collateral.
```
...
align.cell_fabric.remove_duplicates ERROR : Found errors: SHORT: 0 OPEN: 30 DIFFERENT WIDTH: 21
align.cell_fabric.drc ERROR : Found errors: DRC 71
align.cell_fabric.postprocess INFO : Running PostProcessor...
align.pnr.main INFO : OUTPUT json at /home/smburns/DARPA/ALIGN-public/work/test_spatial_filter_working_v1/3_pnr/bottom_plate_4path_beamforming_0.json
align.pnr.main ERROR : 222 LVS / DRC errors found !!!
align.pnr.main INFO : OUTPUT error file at /home/smburns/DARPA/ALIGN-public/work/test_spatial_filter_working_v1/3_pnr/bottom_plate_4path_beamforming_0.errors
```
