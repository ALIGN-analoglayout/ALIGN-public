************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_cascode
* View Name:     schematic
* Netlisted on:  Sep 11 21:06:28 2019
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
* Cell Name:    single_ended_cascode
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_cascode Vbiasn1 Vbiasn2 Vbiasp1 Vbiasp2 Vinn Vinp Voutn
*.PININFO Vbiasn1:I Vbiasn2:I Vbiasp1:I Vbiasp2:I Vinn:I Vinp:I Voutn:O
MM10 net27 net12 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM9 net21 net12 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM8 net12 Vbiasn2 net27 gnd! nmos_rvt w=WA l=LA nfin=nA
MM7 Voutn Vbiasn2 net21 gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 net32 Vinp net10 gnd! nmos_rvt w=WA l=LA nfin=nA
MM0 net26 Vinn net10 gnd! nmos_rvt w=WA l=LA nfin=nA
MM4 net10 Vbiasn1 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM6 net12 Vbiasp2 net26 vdd! pmos_rvt w=WA l=LA nfin=nA
MM5 Voutn Vbiasp2 net32 vdd! pmos_rvt w=WA l=LA nfin=nA
MM1 net32 Vbiasp1 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM2 net26 Vbiasp1 vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_load_biasn Vbiasn1 Vbiasn2 Biasp
*.PININFO Biasp:I Vbiasn1:O Vbiasn2:O
MM15 Vbiasn2 Vbiasn2 Vbiasn1 gnd! nmos_rvt w=WA l=LA nfin=nA
MM13 Vbiasn1 Vbiasn1 gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM14 Vbiasn2 Biasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR14_2 Vbiasn Vbiasp
*.PININFO Vbiasn:O Vbiasp:O
MM2 Vbiasp Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM0 net010 Vbiasn gnd! gnd! nmos_rvt w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
MM1 Vbiasn Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
RR0 Vbiasn net010 res=rK
.ENDS


xiota LG_Vbiasn1 LG_Vbiasn2 LG_Vbiasp1 LG_Vbiasp2 Vinn Vinp Voutn single_ended_cascode
xiLG_load_biasn Biasp LG_Vbiasn1 LG_Vbiasn2 LG_load_biasn
xibCR14_2 Biasn Biasp CR14_2
.END