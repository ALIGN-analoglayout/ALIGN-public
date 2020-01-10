************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_LG
* Top Cell Name: LG_npmos
* View Name:     schematic
* Netlisted on:  Sep 13 00:32:50 2019
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
* Cell Name:    LG_npmos
* View Name:    schematic
************************************************************************

.SUBCKT LG_npmos Biasn Vbiasn Vbiasp
*.PININFO Biasn:I Vbiasn:O Vbiasp:O
MM4 Vbiasp Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM2 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 neta Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasn neta vdd! vdd! pmos w=WA l=LA nfin=nA
MM0 neta neta vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

