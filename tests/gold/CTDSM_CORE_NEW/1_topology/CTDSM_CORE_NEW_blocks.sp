
.subckt CTDSM_CORE_NEW ibias1 vdda vss clkb1 rstb clk clkb2 outm outp vddd vip vim ibias2
xi160 ibias1 vdda vo1m vo1p vo2p vo2m vss Gm1_v5_Practice
xi154 clkb1 net062 vo3m vo3p rstb vdda vss FIR_DAC
xi152 clk net052 vo1p vo1p rstb vdda vss FIR_DAC
xm1 vss clkb2 vss Dcap_NMOS_n12_X1_Y1
xm0 vss clkb1 vss Dcap_NMOS_n12_X1_Y1
xi164 vo1p vo1m C1
xi128 outm outp net072 net071 vddd vss SR_Latch
c6 vo3p vo3m Cap_10f
c3 net074 net073 Cap_10f
r16 vo1p vip Res_100
r51 vo2m net073 Res_100
r25 vo2p net074 Res_100
r47 vo1m vim Res_100
xi161 ibias2 vdda vo2m vo2p vo3p vo3m vss Gm1_v5_Practice
xi88 net062 clk rstb net052 vdda vss DFCNQD2BWP
xi97 outp clkb1 rstb net062 vdda vss DFCNQD2BWP
xi92 net063 clk rstb net051 vdda vss DFCNQD2BWP
xi99 outm clkb2 rstb net063 vdda vss DFCNQD2BWP
xi146 clk vss net072 net071 vddd vo3p vo3m myComparator_v3
xi153 clk net051 vo1m vo1m rstb vdda vss FIR_DAC
xi155 clkb2 net063 vo3p vo3m rstb vdda vss FIR_DAC
.ends CTDSM_CORE_NEW

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CMB_PMOS_2 B DA S DB DC
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
xM0_M1 DA S DB B SCM_PMOS_n12_X1_Y1
.ends CMB_PMOS_2

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt Gm1_v5_Practice ibias vim vip vom vop
xxm8 net074 ntail1 vss vss Switch_NMOS_n12_X1_Y1
xxm2 vdd ibias vdd Dcap_PMOS_n12_X1_Y1
c21 vom ntail1 Cap_10f
c22 vop ntail1 Cap_10f
r12 vop ntail1 Res_100
r11 vom ntail1 Res_100
xxm3 vss ntail1 vss Dcap_NMOS_n12_X1_Y1
xm12_xm14_xm11 ibias vdd vop vom vdd CMB_PMOS_2
xxm27_xm26 vom vip net074 vop vim net074 DP_NMOS_n12_X1_Y1
.ends Gm1_v5_Practice

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dcap_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1

.subckt FIR_DAC clk in r1 r2 rstb
r19 r1 net3 Res_100
r48 r2 in Res_100
xi86 in clk rstb net3 vdd vss DFCNQD2BWP
.ends FIR_DAC

.subckt DFCNQD2BWP d cp cdn q
xm0 net63 cp vss vss Switch_NMOS_n12_X1_Y1
xmi4 net61 net63 vss vss Switch_NMOS_n12_X1_Y1
xm1 net97 cdn net60 vss Switch_NMOS_n12_X1_Y1
xm2 net123 net95 vss vss Switch_NMOS_n12_X1_Y1
xmi29 net49 net63 net17 vss Switch_NMOS_n12_X1_Y1
xmi15 net123 net81 net49 vss Switch_NMOS_n12_X1_Y1
xm3 net60 net49 vss vss Switch_NMOS_n12_X1_Y1
xm4 net97 cdn net21 vss Switch_NMOS_n12_X1_Y1
xm5 net81 net63 vss vss Switch_NMOS_n12_X1_Y1
xmi5 net95 d net61 vss Switch_NMOS_n12_X1_Y1
xmi49 net25 cdn vss vss Switch_NMOS_n12_X1_Y1
xm6 net21 net49 vss vss Switch_NMOS_n12_X1_Y1
xmi26 net17 net97 vss vss Switch_NMOS_n12_X1_Y1
xmi48 net13 net123 net25 vss Switch_NMOS_n12_X1_Y1
xm7 q net97 vss vss Switch_NMOS_n12_X1_Y1
xm8 q net97 vss vss Switch_NMOS_n12_X1_Y1
xmi47 net95 net81 net13 vss Switch_NMOS_n12_X1_Y1
xmi33 net80 net97 vdd vdd Switch_PMOS_n12_X1_Y1
xm9 q net97 vdd vdd Switch_PMOS_n12_X1_Y1
xm10 net97 net49 vdd vdd Switch_PMOS_n12_X1_Y1
xmi43 net101 net123 vdd vdd Switch_PMOS_n12_X1_Y1
xmi6 net95 d net120 vdd Switch_PMOS_n12_X1_Y1
xm11 q net97 vdd vdd Switch_PMOS_n12_X1_Y1
xm12 net97 net49 vdd vdd Switch_PMOS_n12_X1_Y1
xm13 net97 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xmi44 net101 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xm14 net97 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xm15 net123 net95 vdd vdd Switch_PMOS_n12_X1_Y1
xm16 net63 cp vdd vdd Switch_PMOS_n12_X1_Y1
xmi16 net123 net63 net49 vdd Switch_PMOS_n12_X1_Y1
xm17 net81 net63 vdd vdd Switch_PMOS_n12_X1_Y1
xmi32 net49 net81 net80 vdd Switch_PMOS_n12_X1_Y1
xmi45 net95 net63 net101 vdd Switch_PMOS_n12_X1_Y1
xmi7 net120 net81 vdd vdd Switch_PMOS_n12_X1_Y1
.ends DFCNQD2BWP

.subckt C1 a b
c0<3> b a Cap_40f
.ends C1

.subckt SR_Latch q qb r s
xi1 r qb q vdd vss NR2D8BWP
xi0 s q qb vdd vss NR2D8BWP
.ends SR_Latch

.subckt NR2D8BWP a1 a2 zn
xm0 zn a2 vss vss Switch_NMOS_n12_X1_Y1
xm1 zn a1 vss vss Switch_NMOS_n12_X1_Y1
xm2 net13 a2 vdd vdd Switch_PMOS_n12_X1_Y1
xm3 zn a1 net13 vdd Switch_PMOS_n12_X1_Y1
.ends NR2D8BWP

.subckt CCP_PMOS_S_n12_X1_Y1 B DA DB S
xM0 DA DB S B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends CCP_PMOS_S_n12_X1_Y1

.subckt CCP_NMOS_n12_X1_Y1 B DA DB SA SB
xM0 DA DB SA B Switch_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends CCP_NMOS_n12_X1_Y1

.subckt dummy_hier_crossp crossp clk outm
xxm12 crossp clk vdd vdd Switch_PMOS_n12_X1_Y1
xxm8 outm crossp vdd vdd Switch_PMOS_n12_X1_Y1
.ends dummy_hier_crossp

.subckt dummy_hier_crossn outp crossn clk
xxm15 outp crossn vdd vdd Switch_PMOS_n12_X1_Y1
xxm1 crossn clk vdd vdd Switch_PMOS_n12_X1_Y1
.ends dummy_hier_crossn

.subckt myComparator_v3 clk gnd outm outp _net0 _net1
xxm0 gnd intern gnd Dcap_NMOS_n12_X1_Y1
xxm22 gnd interp gnd Dcap_NMOS_n12_X1_Y1
xxm7 net069 clk gnd gnd Switch_NMOS_n12_X1_Y1
xxm18 intern clk vdd vdd Switch_PMOS_n12_X1_Y1
xxm2 interp clk vdd vdd Switch_PMOS_n12_X1_Y1
xxm13_xm14 crossp crossn vdd vdd CCP_PMOS_S_n12_X1_Y1
xxm3_xm4 crossp crossn interp intern gnd CCP_NMOS_n12_X1_Y1
xxm6_xm5 interp _net1 net069 intern _net0 gnd DP_NMOS_n12_X1_Y1
xxm16_xm17 outm crossp gnd outp crossn gnd DP_NMOS_n12_X1_Y1
xm12_xm8 vdd clk outm crossp dummy_hier_crossp
xm15_xm1 crossn vdd clk outp dummy_hier_crossn
.ends myComparator_v3

.subckt CCP_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_PMOS_S_n12_X1_Y1

.subckt CCP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_NMOS_n12_X1_Y1
