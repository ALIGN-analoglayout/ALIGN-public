** Generated for: hspiceD
** Generated on: Jan  5 20:23:09 2020
** Design library name: GF12_telescopic_ota_testbench
** Design cell name: telescopic_ota_ac_testbench_psrr
** Design view name: schematic
.GLOBAL vss! vdd!
.PARAM cload=357f ibias_r=40u vcm_r=0.5 vdd_r=1 wireopt=3


.AC DEC 10 10.0 100e9

.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2
.LIB "HSPICE_MODELS.lib" TT

** Include OTA here
.INC "./telescopic_ota_12nm.sp"

** Library name: GF12_telescopic_ota_testbench
** Cell name: telescopic_ota_ac_testbench_psrr
** View name: schematic
xi0 net07 0 vcm net08 vout net06 vdd! vss! telescopic_ota_12nm
v4 net02 0 DC=vdd_r
v1 net08 vcm AC 100e-6 0
v6 vcm 0 DC=vcm_r
v2 net02 net07 AC 1 0 SIN 0 0
c0 vout 0 cload
i5 net02 net06 DC=ibias_r
.END
