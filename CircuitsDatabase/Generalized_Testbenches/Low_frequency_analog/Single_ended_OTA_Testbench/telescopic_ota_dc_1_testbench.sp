** Design cell name: telescopic_ota_dc_1_testbench
** Design view name: schematic
**************************************************
************ PARAMETER DEFINITION ****************
.GLOBAL vss! vdd!
.PARAM cload=357f 
.PARAM ibias_r=40u 
.PARAM vcm_r=0.5 
.PARAM vdd_r=1 
.PARAM wireopt=3

****************** DC ANALYSIS *******************
.DC vcm_r 200e-3 600e-3 50e-3

***************** OPTIONS *************************
.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2
+    LIST NODE POST


****** INCLUDE YOUR MODEL PATH HERE ***************
.LIB "HSPICE_MODELS.lib" TT

********* INCLUDE YOUR OTA HERE *******************
.INC "./telescopic_ota_12nm.sp"

******** SAVE OPERATING CONDITIONS ****************
.OP 

**************** TESTBENCH ************************
** Cell name: telescopic_ota_dc_testbench
** View name: schematic

xi0 net02 0 net7 net7 net5 net06 vdd! vss! telescopic_ota_12nm
v4 net02 0 DC=vdd_r
v6 net7 0 DC=vcm_r
c0 net5 0 cload
i5 net02 net06 DC=ibias_r

.END
