.subckt ota_asap7 VDD VOUT VSS Input1 Input2 Ids
m5 Ids Ids VSS VSS nmos_rvt w=270e-9 l=20e-9 nfin=12
m4 net10 Ids VSS VSS nmos_rvt w=270e-9 l=20e-9 nfin=48
m3 VOUT Input1 net10 VSS nmos_rvt w=270e-9 l=20e-9 nfin=192
m0 net8 Input2 net10 VSS nmos_rvt w=270e-9 l=20e-9 nfin=192
m2 VOUT net8 VDD VDD pmos_rvt w=270e-9 l=20e-9 nfin=120
m1 net8 net8 VDD VDD pmos_rvt w=270e-9 l=20e-9 nfin=120
.ends ota_asap7


