************************************************************************
* auCdl Netlist:
* 
* Library Name:  RF_LNA
* Top Cell Name: 1_CS_inductive_load
* View Name:     schematic
* Netlisted on:  Mar 13 15:30:22 2019
************************************************************************

*.BIPOLAR
*.RESI = 2000 
*.RESSIZE
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
*.SCALE METER
*.MEGA
.PARAM


*.PIN vdd!
*+    gnd!

************************************************************************
* Library Name: RF_LNA
* Cell Name:    1_CS_inductive_load
* View Name:    schematic
************************************************************************

.SUBCKT test2 Vbias Vin Vout
*.PININFO Vbias:I Vin:I Vout:O
LL0 vdd! Vout 2m
MM0 Vout net5 gnd! gnd! nmos_rvt w=27n l=20n nfin=1
RR0 Vbias net5 5K
RR1 Vdd! net5 5K
CC1 Vin net5 10f
.ENDS

