** Generated for: hspiceD
** Generated on: Nov  1 12:14:13 2019
** Design library name
** Design cell name: 2019_09_16_five_transistor_ota
** Design view name: schematic
.PARAM wireopt=3
.INCLUDE "./five_transistor_OTA.sp"

.OP

.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

xi0 vinn_ota vinp_ota vout_ota id_ota vdd_ota vss_ota five_transistor_OTA
v2 vinn_ota 0 DC=550e-3 AC 500e-3 180
v1 vinp_ota 0 DC=550e-3 AC 500e-3
v0 vdd_ota 0 DC=1000e-3
i5 vdd_ota id_ota DC=40e-6
c1 vout_ota 0 350e-15
v3 vss_ota 0 DC=0

.AC DEC 100 1.0 1e11

.meas ac GAIN find vdb(vout_ota) at = 1       			$ Measure Open-loop Gain    (Gain) 	(dB)
.meas ac UGF when vdb(vout_ota)=0
.meas ac threeDB when par('vdb(vout_ota)+3')=gain				$ Measure Unity-gain Frequency 	(UGF) 	(Hz)
.meas ac PM find par('180+vp(vout_ota)') when vdb(vout_ota)=0		        $ Measure Phase margin	(PM) 	(deg)

.END
