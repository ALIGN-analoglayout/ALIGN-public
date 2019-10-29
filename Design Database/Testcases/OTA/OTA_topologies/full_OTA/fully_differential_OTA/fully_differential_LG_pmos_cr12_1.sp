************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential
* View Name:     schematic
* Netlisted on:  Sep 11 21:04:32 2019
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

.SUBCKT fully_differential Vbiasn Vbiasp Vinn Vinp Voutn Voutp
*.PININFO Vbiasn:I Vbiasp:I Vinn:I Vinp:I Voutn:O Voutp:O
MM1 Voutn Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM2 Voutp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM4 net14 Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 Voutn Vinp net14 gnd! nmos_rvt w=WA l=LA nfin=nA
MM0 Voutp Vinn net14 gnd! nmos_rvt w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_pmos Biasn Vbiasp
*.PININFO Biasn:I Vbiasp:O
MM10 Vbiasp Biasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR12_1 Vbiasn
*.PININFO Vbiasn:O
MM0 Vbiasn Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM1 net10 Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM2 Vbiasn net10 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
RRF vdd! Vbiasn res=rK
RR0 vdd! net10 res=rK
.ENDS


xiota LG_Vbiasn LG_Vbiasp Vinn Vinp Voutn Voutp fully_differential
xiLG_pmos Biasn LG_Vbiasp LG_pmos
xibCR12_1 Biasn CR12_1
.END