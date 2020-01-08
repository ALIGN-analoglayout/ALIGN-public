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


.SUBCKT LG_load_biasp_LV Biasn Vbiasp2
*.PININFO Biasn:I Vbiasp2:O
MM0 Vbiasp2 Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net8 Vbiasp2 vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasp2 Vbiasp2 net8 vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR2_2_wilson Vbiasn Vbiasp
*.PININFO Vbiasn:O Vbiasp:O
RR0 Vbiasn gnd! res=rK
MM2 Vbiasp net12 Vbiasn gnd! nmos w=WA l=LA nfin=nA
MM0 net12 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 net12 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn LG_Vbiasp1 LG_Vbiasp2 Vinn Vinp Voutn Voutp fully_differential_cascode
xiLG_load_biasp_LV Biasn LG_Vbiasp2 LG_load_biasp_LV
xibCR2_2_wilson Biasn Vbiasp CR2_2_wilson
.END