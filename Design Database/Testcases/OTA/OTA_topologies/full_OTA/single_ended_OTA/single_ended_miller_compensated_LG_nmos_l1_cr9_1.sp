************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_miller_compensated
* View Name:     schematic
* Netlisted on:  Sep 11 21:08:39 2019
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
* Cell Name:    single_ended_miller_compensated
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_miller_compensated Vbiasn Vinn Vinp Voutn
*.PININFO Vbiasn:I Vinn:I Vinp:I Voutn:O
MM6 Voutn Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 net011 Vinp net16 gnd! nmos_rvt w=WA l=LA nfin=nA
MM0 net07 Vinn net16 gnd! nmos_rvt w=WA l=LA nfin=nA
MM4 net16 Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM1 net011 net07 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM2 net07 net07 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM5 Voutn net011 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
CC0 Voutn net011 1p $[CP]
.ENDS


.SUBCKT LG_nmos_l1 Biasn Vbiasn Vbiasp
*.PININFO Biasn:I Vbiasn:O Vbiasp:O
MM2 Vbiasn Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM10 Vbiasp Biasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM1 Vbiasn Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM0 Vbiasp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR9_1 Vbiasn
*.PININFO Vbiasn:O
RR1 net05 gnd! res=rK
RRF vdd! Vbiasn res=rK
MM0 Vbiasn Vbiasn net05 gnd! nmos_rvt w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn Vinn Vinp Voutn single_ended_miller_compensated
xiLG_nmos_l1 Biasn LG_Vbiasn LG_Vbiasp LG_nmos_l1
xibCR9_1 Biasn CR9_1
.END