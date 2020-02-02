************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_LG
* Top Cell Name: LG_load_biasn_S1
* View Name:     schematic
* Netlisted on:  Sep 13 00:31:22 2019
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
* Cell Name:    LG_load_biasn_S1
* View Name:    schematic
************************************************************************

.SUBCKT LG_load_biasn_S1 Vbiasn1 Biasp
*.PININFO Biasp:I Vbiasn1:O
MM8 Vbiasn1 Vbiasn1 gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 Vbiasn1 Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

