************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_cascode_current_mirror_pmos
* View Name:     schematic
* Netlisted on:  Sep 11 21:41:22 2019
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
* Cell Name:    single_ended_cascode_current_mirror_pmos
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_cascode_current_mirror_pmos Vbiasn2 Vbiasp Vbiasp2 Vinn 
+ Vinp Voutp
*.PININFO Vbiasn2:I Vbiasp:I Vbiasp2:I Vinn:I Vinp:I Voutp:O
MM14 net025 net012 vdd! vdd! pmos w=WA l=LA nfin=nA
MM13 net024 net012 vdd! vdd! pmos w=WA l=LA nfin=nA
MM3 Voutp Vbiasp2 net025 vdd! pmos w=WA l=LA nfin=nA
MM2 net012 Vbiasp2 net024 vdd! pmos w=WA l=LA nfin=nA
MM7 net11 Vinn net14 net27 pmos w=WA l=LA nfin=nA
MM6 net16 Vinp net14 net27 pmos w=WA l=LA nfin=nA
MM5 net14 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM12 net29 net11 gnd! gnd! nmos w=WA l=LA nfin=nA
MM11 net32 net16 gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 net33 net11 gnd! gnd! nmos w=WA l=LA nfin=nA
MM4 net26 net16 gnd! gnd! nmos w=WA l=LA nfin=nA
MM1 Voutp Vbiasn2 net29 gnd! nmos w=WA l=LA nfin=nA
MM0 net012 Vbiasn2 net32 gnd! nmos w=WA l=LA nfin=nA
MM9 net11 Vbiasn2 net33 gnd! nmos w=WA l=LA nfin=nA
MM8 net16 Vbiasn2 net26 gnd! nmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_load_biasn_LV Vbiasn2 Biasp
*.PININFO Biasp:I Vbiasn2:O
MM13 net9 Vbiasn2 gnd! gnd! nmos w=WA l=LA nfin=nA
MM15 Vbiasn2 Vbiasn2 net9 gnd! nmos w=WA l=LA nfin=nA
MM14 Vbiasn2 Biasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR15_1 Vbiasp
*.PININFO Vbiasp:O
RR1 Vbiasp gnd! res=rK
MM2 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn2 LG_Vbiasp LG_Vbiasp2 Vinn single_ended_cascode_current_mirror_pmos
xiLG_load_biasn_LV Biasp LG_Vbiasn2 LG_load_biasn_LV
xibCR15_1 Biasp CR15_1
.END