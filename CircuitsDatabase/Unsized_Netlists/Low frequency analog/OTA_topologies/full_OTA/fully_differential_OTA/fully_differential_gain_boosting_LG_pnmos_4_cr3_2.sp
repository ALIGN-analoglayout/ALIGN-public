************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential_gain_boosting
* View Name:     schematic
* Netlisted on:  Sep 11 21:05:36 2019
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
* Library Name: OTA_class
* Cell Name:    fully_differential
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential Vinn Vinp Voutn Voutp
*.PININFO Vinn:I Vinp:I Voutn:O Voutp:O
MM1 Voutn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 Voutp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM4 net14 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Voutn Vinp net14 gnd! nmos w=WA l=LA nfin=nA
MM0 Voutp Vinn net14 gnd! nmos w=WA l=LA nfin=nA
.ENDS

************************************************************************
* Library Name: OTA_class
* Cell Name:    fully_differential_gain_boosting
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential_gain_boosting Vbiasn Vbiasp Vinn Vinp Voutn Voutp
*.PININFO Vbiasn:I Vinn:I Vinp:I Vbiasp:O Voutn:O Voutp:O
MM8 Voutn net22 net23 gnd! nmos w=WA l=LA nfin=nA
MM7 Voutp net19 net21 gnd! nmos w=WA l=LA nfin=nA
MM3 net23 Vinp net15 gnd! nmos w=WA l=LA nfin=nA
MM0 net21 Vinn net15 gnd! nmos w=WA l=LA nfin=nA
MM4 net15 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 Voutn net24 net25 vdd pmos w=WA l=LA nfin=nA
MM5 Voutp net20 net12 vdd pmos w=WA l=LA nfin=nA
MM1 net25 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net12 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
XI3 net12 net25 net24 net20 / fully_differential
XI1 net23 net21 net19 net22 / fully_differential
.ENDS


.SUBCKT LG_pnmos_4 Biasp Vbiasn Vbiasp
*.PININFO Biasp:I Vbiasn:O Vbiasp:O
MM1 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM0 Vbiasp net6 gnd! gnd! nmos w=WA l=LA nfin=nA
MM8 net6 net6 gnd! gnd! nmos w=WA l=LA nfin=nA
MM2 Vbiasn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM10 net6 Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR3_2 Vbiasn Vbiasp
*.PININFO Vbiasn:O Vbiasp:O
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
RR0 net15 gnd! res=rK
MM0 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM2 Vbiasp Vbiasn net15 gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn LG_Vbiasp Vinn Vinp Voutn Voutp fully_differential_gain_boosting
xiLG_pnmos_4 Biasp LG_Vbiasn LG_Vbiasp LG_pnmos_4
xibCR3_2 Biasn Biasp CR3_2
.END