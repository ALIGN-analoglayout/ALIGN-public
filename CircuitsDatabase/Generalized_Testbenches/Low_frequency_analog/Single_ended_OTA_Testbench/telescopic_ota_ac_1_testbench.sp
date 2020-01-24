** Design cell name: telescopic_ota_ac_1_testbench
** Design view name: schematic
******* PARAMETER DEFINITION ***************
.GLOBAL vss! vdd!

.PARAM cload=357f 
.PARAM ibias_r=40u 
.PARAM vcm_r=0.5 
.PARAM vdd_r=1 
.PARAM wireopt=3
.PARAM fmin = 10
.PARAM fmax = 1000e9

*** AC Analysis
.AC DEC 10 fmin fmax

.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2
+    POST


**** INCLUDE YOUR PDK MODEL HERE
.LIB "HSPICE_MODELS.lib" TT


** Include OTA here
.INC "./telescopic_ota_12nm.sp"



********* MEASURE COMMANDS **************
.MEAS ac A_DC max vdb(vout) from=fmin to=fmax
.MEAS ac UGF when vdb(vout)=0

.MEAS ac PM find par('180-vp(vout)') at=ugf	
.MEAS ac GM find par('abs(vdb(vout))') when vp(vout)=179


** Library name: GF12_telescopic_ota_testbench
** Cell name: telescopic_ota_ac_1_testbench
** View name: schematic
xi0 net02 0 vinn vinp vout net06 vdd! vss! telescopic_ota_12nm
v4 net02 0 DC=vdd_r
v6 vcm 0 DC=vcm_r
v0 vinn vcm AC 500e-3 0 SIN 0 0
v1 vinp vcm AC 500e-3 180 SIN 0 0
c0 vout 0 cload
i5 net02 net06 DC=ibias_r
.END
