** Generated for: hspiceD
** Generated on: Jan  6 02:20:37 2020
** Design library name: 
** Design cell name: 2019_10_24_simple_SC_converter
** Design view name: schematic
.GLOBAL vdd!
.PARAM wireopt=3
.OP
.TRAN 1e-9 5e-6
.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: 
** Cell name: 2019_10_24_simple_SC_converter
** View name: schematic
v3 vss 0 DC=0
v0 vin 0 DC=1
v2 phi2 0 PULSE 2 0 2.55e-9 25e-12 25e-12 2.4e-9 5e-9
v1 phi1 0 PULSE 2 0 50e-12 25e-12 25e-12 2.4e-9 5e-9
c1 vout 0 capacitor c=1e-9
c0 net1 0 capacitor c=200e-12 
xp0 net1 phi2 vin vdd! pmos m=1 l=14e-9 nfin=40 nf=10 
xp1 vout phi1 net1 vdd! pmos m=1 l=14e-9 nfin=40 nf=10 
r0 vout 0 225
.MEAS TRAN avgcondv AVG V(vin) FROM=3e-6 TO=5e-6
.MEAS TRAN avgcondi AVG I(v0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_cond AVG par('-V(vin)*I(v0)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1v AVG V(phi1) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1i AVG I(v1) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi1 AVG par('-V(phi1)*I(v1)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2v AVG V(phi2) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2i AVG I(v2) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi2 AVG par('-V(phi2)*I(v2)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgoutv AVG V(vout) FROM=3e-6 TO=5e-6
.MEAS TRAN avgouti AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_out AVG par('V(vout)*I(r0)') FROM=3e-6 TO=5e-6
.MEAS efficiency PARAM='pow_out*100/(pow_cond+pow_phi1+pow_phi2)'
.MEAS output_power PARAM='pow_out'
.MEAS output_current AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS output_voltage AVG V(vout) FROM=3e-6 TO=5e-6
.END

