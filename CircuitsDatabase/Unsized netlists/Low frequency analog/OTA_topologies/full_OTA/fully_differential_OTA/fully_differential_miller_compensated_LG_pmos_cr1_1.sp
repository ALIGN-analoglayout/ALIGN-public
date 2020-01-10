************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential_miller_compensated
* View Name:     schematic
* Netlisted on:  Sep 11 21:05:48 2019
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
* Cell Name:    fully_differential_miller_compensated
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential_miller_compensated Vbiasn Vbiasp Vinn Vinp Voutn 
+ Voutp
*.PININFO Vbiasn:I Vbiasp:I Vinn:I Vinp:I Voutn:O Voutp:O
MM7 Voutp net15 vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 net22 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net15 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM5 Voutn net22 vdd! vdd! pmos w=WA l=LA nfin=nA
MM8 Voutp Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net22 Vinp net21 gnd! nmos w=WA l=LA nfin=nA
MM0 net15 Vinn net21 gnd! nmos w=WA l=LA nfin=nA
MM4 net21 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 Voutn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
CC1 Voutp net15 1p $[CP]
CC0 Voutn net22 1p $[CP]
.ENDS


.SUBCKT LG_pmos Biasn Vbiasp
*.PININFO Biasn:I Vbiasp:O
MM10 Vbiasp Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR1_1 Vbiasn
*.PININFO Vbiasn:O
RRF vdd! Vbiasn res=rK
MM0 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn LG_Vbiasp Vinn Vinp Voutn fully_differential_miller_compensated
xiLG_pmos Biasn LG_Vbiasp LG_pmos
xibCR1_1 Biasn CR1_1
.END