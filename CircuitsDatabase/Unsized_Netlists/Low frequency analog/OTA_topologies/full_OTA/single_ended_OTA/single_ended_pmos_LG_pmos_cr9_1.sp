************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_pmos
* View Name:     schematic
* Netlisted on:  Sep 11 21:09:58 2019
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
* Cell Name:    single_ended_pmos
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_pmos Vbiasp Vinn Vinp Voutp
*.PININFO Vbiasp:I Vinn:I Vinp:I Voutp:O
MM9 Voutp net12 gnd! gnd! nmos w=WA l=LA nfin=nA
MM8 net12 net12 gnd! gnd! nmos w=WA l=LA nfin=nA
MM7 Voutp Vinn net10 net14 pmos w=WA l=LA nfin=nA
MM6 net12 Vinp net10 net14 pmos w=WA l=LA nfin=nA
MM5 net10 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_pmos Biasn Vbiasp
*.PININFO Biasn:I Vbiasp:O
MM10 Vbiasp Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR9_1 Vbiasn
*.PININFO Vbiasn:O
RR1 net05 gnd! res=rK
RRF vdd! Vbiasn res=rK
MM0 Vbiasn Vbiasn net05 gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasp Vinn Vinp Voutp single_ended_pmos
xiLG_pmos Biasn LG_Vbiasp LG_pmos
xibCR9_1 Biasn CR9_1
.END