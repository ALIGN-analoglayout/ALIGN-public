************************************************************************
* auCdl Netlist:
* 
* Library Name:  biasing_circuits
* Top Cell Name: CR15_1
* View Name:     schematic
* Netlisted on:  Apr  4 13:53:10 2019
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
* Cell Name:    CR15_1
* View Name:    schematic
************************************************************************

.SUBCKT CR15_1 Vbiasp
*.PININFO Vbiasp:O
RR1 Vbiasp gnd! res=rK
MM2 Vbiasp Vbiasp vdd! vdd! pmos_rvt w=WA l=LA nfin=nA
.ENDS

