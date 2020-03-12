** Design cell name: telescopic_ota_noise_1_testbench
** Design view name: schematic
***************************************************
*********** PARAMETER DEFINTION *******************
.GLOBAL vss! vdd!
.PARAM cload=357f 
.PARAM idc_r=40u 
.PARAM vcm_r=0.5 
.PARAM vdd_r=1 
.PARAM wireopt=3
.PARAM fmin=10
.PARAM fmax=100e9

************* NOISE ANALYSIS **********************
.AC DEC 10 fmin fmax

.NOISE V(vout) v0 0 listckt=1 listsources=on

************** PRINT ******************************
.PRINT NOISE ONOISE INOISE
.PLOT INOISE ONOISE 

**************** OPTIONS **************************
.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2
+    POST

******** INCLUDE YOUR MODEL PATH HERE *************
.LIB "HSPICE_MODELS.lib" TT

************** INCLUDE YOUR OTA HERE **************
.INC "./telescopic_ota_12nm.sp"


************** TESTBENCH **************************
** Cell name: telescopic_ota_noise_1_testbench
** View name: schematic

xi0 net02 0 net010 net04 vout net06 vdd! vss! telescopic_ota_12nm
v8 net03 0 DC=vcm_r
v4 net02 0 DC=vdd_r
e0 net010 net03 VCVS net7 0 0.5
e1 net04 net03 VCVS net7 0 0.5
v0 net7 0 AC 1 0 SIN 0 0
c0 vout 0 cload
i5 net02 net06 DC=idc_r

.END
