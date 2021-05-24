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
schematic2layout.py dummy_design_dir -s bottom_plate_4path_beamforming  -p ../../pdks/Bulk65nm_Mock_PDK/ --gui --flow_start 3_pnr --flow_stop 3_pnr:route -n 40 --skipGDS
```
