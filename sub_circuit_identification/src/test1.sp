** Generated for: hspiceD
** Generated on: Mar 13 15:23:24 2019
** Design library name: RF_LNA
** Design cell name: 1_CS_inductive_load
** Design view name: schematic
.GLOBAL vdd!


.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2


** Library name: RF_LNA
** Cell name: 1_CS_inductive_load
** View name: schematic
l0 vdd! vout 1e-9
m0 vout net5 0 0 nmos_rvt w=27e-9 l=20e-9 nfin=1
r0 vbias net5 1e3
c1 vin net5 10e-15
.ends
