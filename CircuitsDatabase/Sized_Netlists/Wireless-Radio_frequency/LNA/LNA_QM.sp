** Generated for: hspiceD
** Generated on: Jan  5 21:02:24 2020
** Design library name: PhasedArray_WB_copy
** Design cell name: LNA_QM
** Design view name: schematic


.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2


** Library name: PhasedArray_WB_copy
** Cell name: LNA_QM
** View name: schematic
xr5 net011 vaux vdd resistor l=6e-6 w=500e-9 m=1 
xr4 net063 sf_bias vdd resistor l=6e-6 w=500e-9 m=1 
xr10 net0252 vmain vdd resistor l=6e-6 w=500e-9 m=1 
xr3 net033 sf_bias vdd resistor l=6e-6 w=500e-9 m=1 
xc12 net0252 vss vss mimcap lt=16e-6 wt=16e-6 m=1 
xc9 net0252 vss vss mimcap lt=16e-6 wt=16e-6 m=1 
xc6 outn net063 vdd mimcap lt=20e-6 wt=20e-6 m=1 
xc43 in_int net011 vdd mimcap lt=16e-6 wt=16e-6 m=1 
xc5 outp net033 vdd mimcap lt=20e-6 wt=20e-6 m=1 
xc11 net059 vdd vdd mimcap lt=100e-6 wt=50e-6 m=1 
xc8 net047 vdd vdd mimcap lt=100e-6 wt=50e-6 m=1 
xm10 vdd net033 voutp voutp nmos lr=120e-9 wr=2e-6 nr=32 sigma=1 m=1 mismatchflag=0
xm12 vdd net063 voutn voutn nmos lr=120e-9 wr=2e-6 nr=32 sigma=1 m=1 mismatchflag=0
xm4 outn net011 vss vss nmos lr=60e-9 wr=1e-6 nr=10 sigma=1 m=4 mismatchflag=0
xm13 outp net0252 in_int in_int nmos lr=60e-9 wr=1e-6 nr=10 sigma=1 m=1 mismatchflag=0
xr38 net058 net057 vdd resistor l=24e-6 w=3e-6 m=1 
xr0 voutp vss vdd resistor l=20e-6 w=1e-6 m=1 
xr36 net042 net056 vdd resistor l=24e-6 w=3e-6 m=1 
xr35 net056 net055 vdd resistor l=24e-6 w=3e-6 m=1 
xr34 net055 net054 vdd resistor l=24e-6 w=3e-6 m=1 
xr33 net054 net060 vdd resistor l=24e-6 w=3e-6 m=1 
xr41 outn net032 vdd resistor l=24e-6 w=3e-6 m=1 
xr32 net060 outp vdd resistor l=24e-6 w=3e-6 m=1 
xr1 voutn vss vdd resistor l=20e-6 w=1e-6 m=1 
xr40 net032 vdd vdd resistor l=24e-6 w=3e-6 m=1 
xr37 net057 net042 vdd resistor l=24e-6 w=3e-6 m=1 
xr39 vdd net058 vdd resistor l=24e-6 w=3e-6 m=1 
xl8 net047 outp vss ind w=3e-6 rad=45.5e-6 nr=3.75 
xl9 net059 outn vss ind w=3e-6 rad=42.4e-6 nr=3.75 
xl7 in in_int vss ind w=3e-6 rad=30e-6 nr=3.5 
.END
