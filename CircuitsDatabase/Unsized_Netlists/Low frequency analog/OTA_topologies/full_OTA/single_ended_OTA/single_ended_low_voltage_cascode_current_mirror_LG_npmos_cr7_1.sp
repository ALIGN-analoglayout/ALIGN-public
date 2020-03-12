************************************************************************
* auCdl Netlist:
* 
* Library Name:  OTA_class
* Top Cell Name: single_ended_low_voltage_cascode_current_mirror
* View Name:     schematic
* Netlisted on:  Sep 11 21:08:07 2019
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
* Cell Name:    single_ended_low_voltage_cascode_current_mirror
* View Name:    schematic
************************************************************************

.SUBCKT single_ended_low_voltage_cascode_current_mirror Vbiasn Vinn Vinp Voutp
*.PININFO Vbiasn:I Vinn:I Vinp:I Voutp:O
MM3 Voutp Vinp net13 gnd! nmos w=WA l=LA nfin=nA
MM0 net11 Vinn net13 gnd! nmos w=WA l=LA nfin=nA
MM4 net13 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM6 net11 net18 net19 vdd! pmos w=WA l=LA nfin=nA
MM5 Voutp net18 net20 vdd! pmos w=WA l=LA nfin=nA
MM1 net20 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
MM2 net19 net11 vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS


.SUBCKT LG_npmos Biasn Vbiasn Vbiasp
*.PININFO Biasn:I Vbiasn:O Vbiasp:O
MM4 Vbiasp Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM2 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM10 neta Biasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM3 Vbiasp Vbiasp vdd! vdd! pmos w=WA l=LA nfin=nA
MM1 Vbiasn neta vdd! vdd! pmos w=WA l=LA nfin=nA
MM0 neta neta vdd! vdd! pmos w=WA l=LA nfin=nA
.ENDS

.SUBCKT CR7_1 Vbiasn
*.PININFO Vbiasn:O
RR1 Vbiasn net7 res=rK
RR0 vdd! net7 res=rK
RRF vdd! Vbiasn res=rK
MM1 net7 Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
MM0 Vbiasn Vbiasn gnd! gnd! nmos w=WA l=LA nfin=nA
.ENDS


xiota LG_Vbiasn Vinn Vinp Voutp single_ended_low_voltage_cascode_current_mirror
xiLG_npmos Biasn LG_Vbiasn LG_Vbiasp LG_npmos
xibCR7_1 Biasn CR7_1
.END