************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_two_stage
* View Name:     schematic
* Netlisted on:  Sep 11 21:10:37 2019
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
* Cell Name:    single_ended_two_stage
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_two_stage Vbiasn Vinn Vinp Voutp
*.PININFO Vbiasn:I Vinn:I Vinp:I Voutp:O
MM1 net16 net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net12 net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM9 net9 net12 vdd! vdd! pmos w=WA l=LA nfin=nA
MM5 Voutp net16 vdd! vdd! pmos w=WA l=LA nfin=nA
MM7 net9 net9 gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net16 Vinp net15 gnd! nmos w=WA l=LA nfin=nA
MM0 net12 Vinn net15 gnd! nmos w=WA l=LA nfin=nA
MM4 net15 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 Voutp net9 gnd! gnd! nmos w=WA l=LA nfin=nA
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


xiota LG_Vbiasn Vinn Vinp Voutp single_ended_two_stage
xiLG_nmos_l1 Biasn LG_Vbiasn LG_Vbiasp LG_nmos_l1
xibCR1_1 Biasn CR1_1
.END