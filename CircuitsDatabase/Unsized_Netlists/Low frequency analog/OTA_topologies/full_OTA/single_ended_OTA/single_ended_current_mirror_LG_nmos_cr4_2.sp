************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_current_mirror
* View Name:     schematic
* Netlisted on:  Sep 11 21:07:33 2019
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
* Cell Name:    single_ended_current_mirror
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_current_mirror Vbiasn Vinn Vinp Voutn
*.PININFO Vbiasn:I Vinn:I Vinp:I Voutn:O
MM8 net9 net9 gnd! gnd! nmos w=WA l=LA nfin=nA
MM7 Voutn net9 gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net20 Vinp net16 gnd! nmos w=WA l=LA nfin=nA
MM0 net11 Vinn net16 gnd! nmos w=WA l=LA nfin=nA
MM4 net16 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 net9 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
MM5 Voutn net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 net20 net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net11 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_nmos Biasp Vbiasn
*.PININFO Biasp:I Vbiasn:O
MM8 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 Vbiasn Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
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


xiota LG_Vbiasn Vinn Vinp Voutn single_ended_current_mirror
xiLG_nmos Biasp LG_Vbiasn LG_nmos
xibCR4_2 Biasn Biasp CR4_2
.END