************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_miller_compensated_pmos
* View Name:     schematic
* Netlisted on:  Sep 11 21:09:34 2019
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
* Cell Name:    single_ended_miller_compensated_pmos
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_miller_compensated_pmos Vbiasp Vinn Vinp Voutp
*.PININFO Vbiasp:I Vinn:I Vinp:I Voutp:O
MM13 Voutp net38 gnd! gnd! nmos w=WA l=LA nfin=nA
MM9 net38 net35 gnd! gnd! nmos w=WA l=LA nfin=nA
MM8 net35 net35 gnd! gnd! nmos w=WA l=LA nfin=nA
MM12 Voutp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM11 net33 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM10 net38 Vinn net33 net39 pmos w=WA l=LA nfin=nA
MM7 net35 Vinp net33 net39 pmos w=WA l=LA nfin=nA
CC2 Voutp net38 1p $[CP]
.ENDS


.SUBCKT LG_nmos_l1 Biasn Vbiasn Vbiasp
*.PININFO Biasn:I Vbiasn:O Vbiasp:O
MM2 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 Vbiasp Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM1 Vbiasn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM0 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR1_1 Vbiasn
*.PININFO Vbiasn:O
RRF vdd! Vbiasn res=rK
MM0 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasp Vinn Vinp Voutp single_ended_miller_compensated_pmos
xiLG_nmos_l1 Biasn LG_Vbiasn LG_Vbiasp LG_nmos_l1
xibCR1_1 Biasn CR1_1
.END