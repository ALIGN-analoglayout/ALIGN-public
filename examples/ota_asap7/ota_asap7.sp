.subckt ota_asap7 VDD VOUT VSS Input1 Input2 Ids
m5 Ids Ids net5s VSS nmos_rvt w=270e-9 l=20e-9 nfin=10
m5s net5s Ids VSS VSS nmos_rvt w=270e-9 l=20e-9 nfin=10
m4 net10 Ids net4s VSS nmos_rvt w=270e-9 l=20e-9 nfin=40
m4s net4s Ids VSS VSS nmos_rvt w=270e-9 l=20e-9 nfin=40
m3 VOUT Input1 net3s VSS nmos_rvt w=270e-9 l=20e-9 nfin=160
m3s net3s Input1 net10 VSS nmos_rvt w=270e-9 l=20e-9 nfin=160
m0 net8 Input2 net0s VSS nmos_rvt w=270e-9 l=20e-9 nfin=160
m0s net0s Input2 net10 VSS nmos_rvt w=270e-9 l=20e-9 nfin=160
m2 VOUT net8 net2s VDD pmos_rvt w=270e-9 l=20e-9 nfin=100
m2s net2s net8 VDD VDD pmos_rvt w=270e-9 l=20e-9 nfin=100
m1 net8 net8 net1s VDD pmos_rvt w=270e-9 l=20e-9 nfin=100
m1s net1s net8 VDD VDD pmos_rvt w=270e-9 l=20e-9 nfin=100
.ends ota_asap7


