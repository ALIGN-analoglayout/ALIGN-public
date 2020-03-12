************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential_cascode_pmos
* View Name:     schematic
* Netlisted on:  Sep 11 21:05:09 2019
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
* Library Name: OTA_class
* Cell Name:    fully_differential_cascode_pmos
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential_cascode_pmos Vbiasn1 Vbiasn2 Vbiasp Vinn Vinp 
+ Voutp1 Voutp2
*.PININFO Vbiasp:I Vinn:I Vinp:I Vbiasn1:O Vbiasn2:O Voutp1:O Voutp2:O
MM1 Voutp2 Vbiasn2 net17 gnd! nmos w=WA l=LA nfin=nA
MM0 Voutp1 Vbiasn2 net18 gnd! nmos w=WA l=LA nfin=nA
MM9 net18 Vbiasn1 gnd! gnd! nmos w=WA l=LA nfin=nA
MM8 net17 Vbiasn1 gnd! gnd! nmos w=WA l=LA nfin=nA
MM5 net13 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM7 Voutp1 Vinn net13 net20 pmos w=WA l=LA nfin=nA
MM6 Voutp2 Vinp net13 net20 pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_load_biasn_LV Vbiasn2 Biasp
*.PININFO Biasp:I Vbiasn2:O
MM13 net9 Vbiasn2 gnd! gnd! nmos w=WA l=LA nfin=nA
MM15 Vbiasn2 Vbiasn2 net9 gnd! nmos w=WA l=LA nfin=nA
MM14 Vbiasn2 Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR4_2 Vbiasn Vbiasp
*.PININFO Vbiasn:O Vbiasp:O
MM11 net023 net024 Vbiasn gnd! nmos w=27.0n l=LA nfin=nA
MM8 net025 net010 net023 gnd! nmos w=27.0n l=LA nfin=nA
MM9 net024 net024 net023 gnd! nmos w=27.0n l=LA nfin=nA
MM7 net010 net010 net025 gnd! nmos w=WA l=LA nfin=nA
MM2 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM0 Vbiasp net025 gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 net024 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM4 net010 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM3 Vbiasn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn1 LG_Vbiasn2 LG_Vbiasp Vinn Vinp fully_differential_cascode_pmos
xiLG_load_biasn_LV Biasp LG_Vbiasn2 LG_load_biasn_LV
xibCR4_2 Biasn Biasp CR4_2
.END