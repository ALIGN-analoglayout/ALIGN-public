************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential_pmos
* View Name:     schematic
* Netlisted on:  Sep 11 21:06:01 2019
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
* Cell Name:    fully_differential_pmos
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential_pmos Vbiasn Vbiasp Vinn Vinp Voutn Voutp
*.PININFO Vbiasp:I Vinn:I Vinp:I Vbiasn:O Voutn:O Voutp:O
MM7 Voutp Vinn net12 net16 pmos_rvt w=WA l=LA nfin=nA
MM6 Voutn Vinp net12 net16 pmos_rvt w=WA l=LA nfin=nA
MM5 net12 Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM9 Voutp Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM8 Voutn Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_nmos Biasp Vbiasn
*.PININFO Biasp:I Vbiasn:O
MM8 Vbiasn Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM10 Vbiasn Biasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR6_3 Vbiasn1 Vbiasn2 Vbiasp
*.PININFO Vbiasn1:O Vbiasn2:O Vbiasp:O
MM2 Vbiasp Vbiasn2 Vbiasn1 gnd! nmos_rvt w=WA l=LA nfin=nA
MM0 Vbiasn2 Vbiasn1 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM4 Vbiasn1 net15 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM5 net15 net15 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM1 Vbiasn2 Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM6 net15 Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn LG_Vbiasp Vinn Vinp Voutn Voutp fully_differential_pmos
xiLG_nmos Biasp LG_Vbiasn LG_nmos
xibCR6_3 Biasn1 Biasn2 Biasp CR6_3
.END