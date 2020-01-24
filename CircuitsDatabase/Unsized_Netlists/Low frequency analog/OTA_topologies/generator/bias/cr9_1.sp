************************************************************************
* auCdl Netlist:
* 
* Library Name:  biasing_circuits
* Top Cell Name: CR9_1
* View Name:     schematic
* Netlisted on:  Apr  4 13:52:46 2019
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
* Library Name: biasing_circuits
* Cell Name:    CR9_1
* View Name:    schematic
************************************************************************

.SUBCKT CR9_1 Vbiasn
*.PININFO Vbiasn:O
RR1 net05 gnd! res=rK
RRF vdd! Vbiasn res=rK
MM0 Vbiasn Vbiasn net05 gnd! nmos w=WA l=LA nfin=nA
.ENDS

