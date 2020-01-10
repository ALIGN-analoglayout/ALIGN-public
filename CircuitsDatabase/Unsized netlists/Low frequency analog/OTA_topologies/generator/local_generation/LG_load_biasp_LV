************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_LG
* Top Cell Name: LG_load_biasp_LV
* View Name:     schematic
* Netlisted on:  Sep 13 00:31:47 2019
************************************************************************

*.BIPOLAR
*.RESI = 2000 
*.RESVAL
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
*.SCALE METER
*.MEGA
.PARAM

*.GLOBAL vdd!
+        gnd!

*.PIN vdd!
*+    gnd!

************************************************************************
* Library Name: OTA_LG
* Cell Name:    LG_load_biasp_LV
* View Name:    schematic
************************************************************************

.SUBCKT LG_load_biasp_LV Biasn Vbiasp2
*.PININFO Biasn:I Vbiasp2:O
MM0 Vbiasp2 Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net8 Vbiasp2 vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasp2 Vbiasp2 net8 vdd! pmos w=WA l=LA nfin=nA
.ENDS

