************************************************************************
* auCdl Netlist:
*
* Library Name: Test
* Cell Name:    test
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
* Library Name: Test
* Cell Name:    test
* View Name:    schematic
************************************************************************

.SUBCKT test2 Vbias Vin Vout
*.PININFO Vbias:I Vin:I Vout:O
MM0 Vout net5 gnd! gnd! nmos_rvt w=27n l=20n nfin=1
MM2 Vout net2 net3 gnd! n w=27n l=20n nfin=1
MM3 Vout net3 net4 gnd! nfet w=27n l=20n nfin=1
RR0 Vbias net5 5K
CC0 Vin net5 10f
LL0 vdd! Vout 2m
RR1 Vbias net6 resistor r=5K
CC1 Vin net6 capacitor w=100n l=100n
LL1 vdd! net6 inductor ind=2m
.ENDS

