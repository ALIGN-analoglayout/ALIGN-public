** Generated for: hspiceD
** Generated on: Nov 10 15:48:14 2018
** Design library name: DC_converter
** Design cell name: 
** Design view name: schematic
.GLOBAL vdd!


.TEMP 25.0

.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: DC_converter
** Cell name: 2018_11_09_ota
** View name: schematic
m5 net2 net2 net5s 0 nmos w=270e-9 l=20e-9 nfin=10
m5s net5s net2 0 0 nmos w=270e-9 l=20e-9 nfin=10
m4 net10 net2 net4s 0 nmos w=270e-9 l=20e-9 nfin=40
m4s net4s net2 0 0 nmos w=270e-9 l=20e-9 nfin=40
m3 vout net15 net3s 0 nmos w=270e-9 l=20e-9 nfin=160
m3s net3s net15 net10 0 nmos w=270e-9 l=20e-9 nfin=160
m0 net8 net17 net0s 0 nmos w=270e-9 l=20e-9 nfin=160
m0s net0s net17 net10 0 nmos w=270e-9 l=20e-9 nfin=160
m2 vout net8 net2s vdd pmos w=270e-9 l=20e-9 nfin=100
m2s net2s net8 vdd vdd pmos w=270e-9 l=20e-9 nfin=100
m1 net8 net8 net1s vdd pmos w=270e-9 l=20e-9 nfin=100
m1s net1s net8 vdd vdd pmos w=270e-9 l=20e-9 nfin=100

**testbench
v2 net15 0 DC=675e-3 AC 500e-3 180
v1 net17 0 DC=675e-3 AC 500e-3
v0 vdd 0 DC=1000e-3
i5 vdd net2 DC=10e-6
c1 vout 0 175e-15

.OP

.AC DEC 100 1.0 1e11

.DC vdd! 1000e-3 1100e-3 200e-3

.meas dc current avg i(v0)
**.meas ac gm find i(c1) at =1
.meas ac GAIN find vdb(vout) at = 1       			$ Measure Open-loop Gain    (Gain) 	(dB)
.meas ac UGF when vdb(vout)=0
.meas ac threeDB when par('vdb(vout)+3')=gain				$ Measure Unity-gain Frequency 	(UGF) 	(Hz)
.meas ac PM find par('180+vp(vout)') when vdb(vout)=0		        $ Measure Phase margin	(PM) 	(deg)

.END
