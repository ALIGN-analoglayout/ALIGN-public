************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_LG
* Top Cell Name: LG_load_biasn
* View Name:     schematic
* Netlisted on:  Sep 13 00:30:40 2019
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
* Cell Name:    LG_load_biasn
* View Name:    schematic
************************************************************************

.SUBCKT LG_load_biasn Vbiasn1 Vbiasn2 Biasp
*.PININFO Biasp:I Vbiasn1:O Vbiasn2:O
MM15 Vbiasn2 Vbiasn2 Vbiasn1 gnd! nmos w=WA l=LA nfin=nA
MM13 Vbiasn1 Vbiasn1 gnd! gnd! nmos w=WA l=LA nfin=nA
MM14 Vbiasn2 Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

