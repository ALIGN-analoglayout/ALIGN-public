************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: fully_differential_cascode
* View Name:     schematic
* Netlisted on:  Sep 11 21:04:46 2019
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
* Cell Name:    fully_differential_cascode
* View Name:    schematic
************************************************************************

.SUBCKT fully_differential_cascode Vbiasn Vbiasp1 Vbiasp2 Vinn Vinp Voutn Voutp
*.PININFO Vbiasn:I Vbiasp1:I Vbiasp2:I Vinn:I Vinp:I Voutn:O Voutp:O
MM3 Voutn Vinp net16 gnd! nmos w=WA l=LA nfin=nA
MM0 Voutp Vinn net16 gnd! nmos w=WA l=LA nfin=nA
MM4 net16 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 Voutp Vbiasp2 net22 vdd! pmos w=WA l=LA nfin=nA
MM5 Voutn Vbiasp2 net21 vdd! pmos w=WA l=LA nfin=nA
MM1 net21 Vbiasp1 vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net22 Vbiasp1 vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_load_biasp Biasn Vbiasp1 Vbiasp2
*.PININFO Biasn:I Vbiasp1:O Vbiasp2:O
MM0 Vbiasp2 Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM1 Vbiasp2 Vbiasp2 Vbiasp1 vdd! pmos w=WA l=LA nfin=nA
MM3 Vbiasp1 Vbiasp1 vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR7_1 Vbiasn
*.PININFO Vbiasn:O
RR1 Vbiasn net7 res=rK
RR0 vdd! net7 res=rK
RRF vdd! Vbiasn res=rK
MM1 net7 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM0 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn LG_Vbiasp1 LG_Vbiasp2 Vinn Vinp Voutn Voutp fully_differential_cascode
xiLG_load_biasp Biasn LG_Vbiasp1 LG_Vbiasp2 LG_load_biasp
xibCR7_1 Biasn CR7_1
.END