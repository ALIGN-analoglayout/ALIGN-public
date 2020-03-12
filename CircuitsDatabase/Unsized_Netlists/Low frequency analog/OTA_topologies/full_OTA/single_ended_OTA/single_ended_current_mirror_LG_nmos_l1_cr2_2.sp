************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_current_mirror
* View Name:     schematic
* Netlisted on:  Sep 11 21:07:33 2019
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
* Cell Name:    single_ended_current_mirror
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_current_mirror Vbiasn Vinn Vinp Voutn
*.PININFO Vbiasn:I Vinn:I Vinp:I Voutn:O
MM8 net9 net9 gnd! gnd! nmos w=WA l=LA nfin=nA
MM7 Voutn net9 gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 net20 Vinp net16 gnd! nmos w=WA l=LA nfin=nA
MM0 net11 Vinn net16 gnd! nmos w=WA l=LA nfin=nA
MM4 net16 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 net9 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
MM5 Voutn net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 net20 net20 vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net11 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_nmos_l1 Biasn Vbiasn Vbiasp
*.PININFO Biasn:I Vbiasn:O Vbiasp:O
MM2 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 Vbiasp Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM1 Vbiasn Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM0 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR2_2_wilson Vbiasn Vbiasp
*.PININFO Vbiasn:O Vbiasp:O
RR0 Vbiasn gnd! res=rK
MM2 Vbiasp net12 Vbiasn gnd! nmos w=WA l=LA nfin=nA
MM0 net12 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 net12 Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn Vinn Vinp Voutn single_ended_current_mirror
xiLG_nmos_l1 Biasn LG_Vbiasn LG_Vbiasp LG_nmos_l1
xibCR2_2_wilson Biasn Vbiasp CR2_2_wilson
.END