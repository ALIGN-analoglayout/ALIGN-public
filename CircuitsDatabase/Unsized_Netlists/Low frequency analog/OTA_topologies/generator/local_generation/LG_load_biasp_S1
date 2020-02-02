************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_LG
* Top Cell Name: LG_load_biasp_S1
* View Name:     schematic
* Netlisted on:  Sep 13 00:31:58 2019
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

*.GLOBAL gnd!
+        vdd!

*.PIN gnd!
*+    vdd!

************************************************************************
* Library Name: OTA_LG
* Cell Name:    LG_load_biasp_S1
* View Name:    schematic
************************************************************************

.SUBCKT LG_load_biasp_S1 Biasn Vbiasp1
*.PININFO Biasn:I Vbiasp1:O
MM3 Vbiasp1 Vbiasp1 vdd! vdd! pmos w=WA l=LA nfin=nA
MM0 Vbiasp1 Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
.ENDS

