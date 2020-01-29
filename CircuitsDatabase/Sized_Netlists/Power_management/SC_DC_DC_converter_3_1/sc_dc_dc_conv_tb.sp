** Generated for: hspiceD
** Generated on: Dec 20 18:33:51 2019
** Design library name:_14nm_test1
** Design cell name: 2019_12_18_SC_DC_DC_converter_ideal
** Design view name: schematic

.PARAM wireopt=3
.INCLUDE "sc_dc_dc_conv_schematic.sp"
.OP
.TRAN 1e-9 5e-6
.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST


** Library name:_14nm_test1
** Cell name: 2019_12_18_SC_DC_DC_converter_ideal
** View name: schematic
r0 vout 0 125
c2 vout 0 1e-6
v4 vdd 0 DC=2
v3 vss 0 DC=0
v0 vin 0 DC=2
v5 phi2_bar 0 PULSE 0 2 2.55e-9 25e-12 25e-12 2.4e-9 5e-9
v2 phi2 0 PULSE 2 0 2.55e-9 25e-12 25e-12 2.4e-9 5e-9
v1 phi1 0 PULSE 2 0 50e-12 25e-12 25e-12 2.4e-9 5e-9
xi0 phi1 phi2 phi2_bar vout vin vss vdd sc_dc_dc_converter
.MEAS TRAN avgcondv AVG V(vin) FROM=3e-6 TO=5e-6
.MEAS TRAN avgcondi AVG I(v0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_cond AVG par('-V(vin)*I(v0)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1v AVG V(phi1) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1i AVG I(v1) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi1 AVG par('-V(phi1)*I(v1)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2v AVG V(phi2) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2i AVG I(v2) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi2 AVG par('-V(phi2)*I(v2)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2barv AVG V(phi2_bar) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2bari AVG I(v5) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi2_bar AVG par('-V(phi2_bar)*I(v5)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgoutv AVG V(vout) FROM=3e-6 TO=5e-6
.MEAS TRAN avgouti AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_out AVG par('V(vout)*I(r0)') FROM=3e-6 TO=5e-6
.MEAS efficiency PARAM='pow_out*100/(pow_cond+pow_phi1+pow_phi2+pow_phi2_bar)'
.MEAS output_power PARAM='pow_out'
.MEAS output_current AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS output_voltage AVG V(vout) FROM=3e-6 TO=5e-6
.END
