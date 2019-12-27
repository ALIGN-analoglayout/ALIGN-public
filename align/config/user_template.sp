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

.subckt CMB_NMOS_2 D0 D1 D2 S
M0 (D0 D0 S B) NMOS_VTL w=w l=90n
M1 (D1 D0 S B) NMOS_VTL w=w l=90n
M2 (D2 D0 S B) NMOS_VTL w=w l=90n
.ends CMB_NMOS_2 

.subckt CMB_NMOS_3 D0 D1 D2 D3 S
M0 (D0 D0 S vss) NMOS_VTL w=w l=90n
M1 (D1 D0 S B) NMOS_VTL w=w l=90n
M2 (D2 D0 S B) NMOS_VTL w=w l=90n
M3 (D3 D0 S B) NMOS_VTL w=w l=90n
.ends CMB_NMOS_3 

.subckt CMB_NMOS_4 D0 D1 D2 D3 D4 S
M0 (D0 D0 S B) NMOS_VTL w=w l=90n
M1 (D1 D0 S B) NMOS_VTL w=w l=90n
M2 (D2 D0 S B) NMOS_VTL w=w l=90n
M3 (D3 D0 S B) NMOS_VTL w=w l=90n
M4 (D4 D0 S B) NMOS_VTL w=w l=90n
.ends CMB_NMOS_4

.subckt INV_LVT i zn SN SP
xm0 zn i SN SN lvtnfet w=w0 l=l0
xm1 zn i SP SP lvtpfet w=w1 l=l0
.ends INV_LVT

.subckt switched_capacitor_combination Vin agnd Vin_ota Voutn phi1 phi2
m0 Voutn phi1 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m7 Vin_ota phi1 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m6 net72 phi1 Vin vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m3 agnd phi2 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m5 agnd phi2 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m4 net72 phi2 agnd vss nmos_rvt w=270e-9 l=20e-9 nfin=5
c3 Vin_ota Voutn 60e-15
c1 net63 net67 30e-15
c0 net72 net63 60e-15
.ends switched_capacitor_combination

**.subckt res_array_8 MINUS0 PLUS0 PLUS1 PLUS2 PLUS3 PLUS4 PLUS5 PLUS6 PLUS7
**r0 PLUS0 MINUS0 500
**r1 PLUS1 PLUS0 1e3
**r2 PLUS2 PLUS1 1e3
**r3 PLUS3 PLUS2 1e3
**r4 PLUS4 PLUS3 1e3
**r5 PLUS5 PLUS4 1e3
**r6 PLUS6 PLUS5 1e3
**r7 PLUS7 PLUS6 500
**.ends res_array_8

.subckt SCM_NMOS_C DA DB S
M0 (DA DA S B) NMOS w=w l=90n
M1 (DB DA S B) NMOS w=w l=90n
C0 (DA S) cap cap=1f
.ends SCM_NMOS_C

.subckt SCM_PMOS_C DA DB S
M0 (DA DA S B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
C0 (DA S) cap cap =1f
.ends SCM_PMOS_C

.subckt SCM_NMOS_RC DA DB S
M0 (DA DA S B) NMOS w=w l=90n
M1 (DB GB S B) NMOS w=w l=90n
C0 (GB S) cap cap=1f
R0 (GB DA) res res=1k
.ends SCM_NMOS_RC

.subckt SCM_PMOS_RC DA DB GA S
M0 (DA GA S B) NMOS w=w l=90n
M1 (DB GB S B) NMOS w=w l=90n
C0 (GB S) cap cap=1f
R0 (GB DA) res res=1k
C1 (DA net1) cap cap=1f
R1 (net1 GA) res res=1k
.ends SCM_NMOS_RC

**.subckt SCM_PMOS_RC DA DB GA S
**M0 (DA GA S B) NMOS w=w l=90n
**M1 (DB GB S B) NMOS w=w l=90n
**C0 (GB S) cap
**R0 (GB DA) res
**C1 (DA net1) cap
**R1 (net1 GA) res
**.ends SCM_NMOS_RC
