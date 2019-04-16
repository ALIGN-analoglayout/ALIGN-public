************************************************************************
* auCdl Netlist:
* 
* Library Name:  pcell
* Top Cell Name: SCM_NMOS_50
* View Name:     schematic
* Netlisted on:  Nov 27 19:13:35 2018
************************************************************************

*.EQUATION
*.SCALE METER
*.MEGA
*.PARAM



************************************************************************
* Library Name: pcell
* Cell Name:    SCM_NMOS_50
* View Name:    schematic
************************************************************************

.SUBCKT SCM_NMOS_50 D1 D2 S 
*.PININFO D1:B D2:B S:B VDD:B VSS:B
MM5 D2 D1 net018 net018 nmos_rvt w=270.0n l=20n nfin=10
MM6 D2 D1 net021 net021 nmos_rvt w=270.0n l=20n nfin=10
MM7 net021 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM8 D2 D1 net023 net023 nmos_rvt w=270.0n l=20n nfin=10
MM9 net023 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM4 net018 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM3 D2 D1 net015 net015 nmos_rvt w=270.0n l=20n nfin=10
MM2 net015 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM1 D2 D1 net09 net09 nmos_rvt w=270.0n l=20n nfin=10
MM0 net09 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM20 net026 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM21 D2 D1 net026 net026 nmos_rvt w=270.0n l=20n nfin=10
MM22 D2 D1 net029 net029 nmos_rvt w=270.0n l=20n nfin=10
MM23 net029 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM30 net039 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM31 net036 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM32 net033 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM35 D2 D1 net039 net039 nmos_rvt w=270.0n l=20n nfin=10
MM36 D2 D1 net036 net036 nmos_rvt w=270.0n l=20n nfin=10
MM37 D2 D1 net033 net033 nmos_rvt w=270.0n l=20n nfin=10
MM19 net047 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM18 net042 D1 S S nmos_rvt w=270.0n l=20n nfin=10
MM17 D1 D1 net047 net047 nmos_rvt w=270.0n l=20n nfin=10
MM16 D1 D1 net042 net042 nmos_rvt w=270.0n l=20n nfin=10
.ENDS

