.subckt CASCODED_SCM_NMOS DA DC GA S
M0 (DA GA DB B) NMOS w=w l=90n
M1 (DB DA S B) NMOS w=w l=90n
M2 (DC DA S B) NMOS w=w l=90n
.ends CASCODED_SCM_NMOS

.subckt CASCODED_SCM_PMOS DA DC GA S
M0 (DA GA DB B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
M2 (DC DA S B) PMOS w=w l=90n
.ends CASCODED_SCM_PMOS

.subckt CASCODED_CMB_NMOS_2 DA DD DC GA S
M0 (DA GA DB B) NMOS w=w l=90n
M1 (DB DA S B) NMOS w=w l=90n
M2 (DC DA S B) NMOS w=w l=90n
M3 (DD DA S B) NMOS w=w l=90n
.ends CASCODED_CMB_NMOS_2

.subckt CASCODED_CMB_PMOS_2 DA DC DD GA S
M0 (DA GA DB B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
M2 (DC DA S B) PMOS w=w l=90n
M3 (DD DA S B) PMOS w=w l=90n
.ends CASCODED_CMB_PMOS_2

.subckt CASCODED_CMB_PMOS_3 DA DC DD DE GA S
M0 (DA GA DB B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
M2 (DC DA S B) PMOS w=w l=90n
M3 (DD DA S B) PMOS w=w l=90n
M4 (DE DA S B) PMOS w=w l=90n
.ends CASCODED_CMB_PMOS_3

.subckt CMB_NMOS_2 D0 D1 D2 S
M0 (D0 D0 S B) NMOS_VTL w=w l=90n
M1 (D1 D0 S B) NMOS_VTL w=w l=90n
M2 (D2 D0 S B) NMOS_VTL w=w l=90n
.ends CMB_NMOS_2 

.subckt CMB_NMOS_3 D0 D1 D2 D3 S
M0 (D0 D0 S B) NMOS_VTL w=w l=90n
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

.subckt INV_LVT i zn BN BP
xm0 zn i SN BN lvtnfet w=w0 l=l0
xm1 zn i SP BP lvtpfet w=w1 l=l0
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

.subckt tgate GA GB D S BN BP
M0 (D GA S BN) NMOS w=w l=90n
M1 (D GB S BP) PMOS w=w l=90n
.ends tgate

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
