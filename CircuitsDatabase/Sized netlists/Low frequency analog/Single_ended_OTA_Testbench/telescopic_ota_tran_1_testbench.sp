** Generated for: hspiceD
** Generated on: Jan  5 20:02:02 2020
** Design library name: GF12_telescopic_ota_testbench
** Design cell name: telescopic_ota_sr_testbench
** Design view name: schematic
.GLOBAL vss! vdd!
.PARAM _expr_1=2e-09 ugf=1G vicm=0.05 cload=357f ibias_r=40u vcm_r=0.5 
+	vdd_r=1 wireopt=3


.TRAN 1e-12 _EXPR_1 START=0.0

.OP

.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2
+    POST

.LIB "HSPICE_MODELS.lib" TT

** Include OTA here
.INC "./telescopic_ota_12nm.sp"

** Library name: GF12_telescopic_ota_testbench
** Cell name: telescopic_ota_sr_testbench
** View name: schematic
xi0 net02 0 vout vinp vout net06 vdd! vss! telescopic_ota_12nm
v4 net02 0 DC=vdd_r
v6 net7 0 DC=vcm_r
v0 vinp net7 PWL 0 0 100e-12 0 110e-12 '-vicm/2' '1/ugf' '-vicm/2' '1/ugf+100e-12' 'vicm/2' TD=0
c0 vout 0 cload
i5 net02 net06 DC=ibias_r
.END
