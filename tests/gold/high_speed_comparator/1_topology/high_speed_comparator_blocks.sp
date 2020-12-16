
.subckt CCP_PMOS_S_n12_X2_Y2 B DA DB S
xM0 DA DB S B Switch_PMOS_n12_X2_Y2
xM1 DB DA S B Switch_PMOS_n12_X2_Y2
.ends CCP_PMOS_S_n12_X2_Y2

.subckt Switch_PMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
.ends Switch_PMOS_n12_X2_Y2

.subckt CCP_NMOS_n12_X4_Y2 B DA DB SA SB
xM0 DA DB SA B Switch_NMOS_n12_X4_Y2
xM1 DB DA SB B Switch_NMOS_n12_X4_Y2
.ends CCP_NMOS_n12_X4_Y2

.subckt Switch_NMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=96
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=96
.ends Switch_NMOS_n12_X4_Y2

.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X4_Y4 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X4_Y4
xM1 DB GB S B Switch_NMOS_n12_X4_Y4
.ends DP_NMOS_n12_X4_Y4

.subckt Switch_NMOS_n12_X4_Y4 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=192
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=192
.ends Switch_NMOS_n12_X4_Y4

.subckt high_speed_comparator clk vdd_nom_123 vop von vss vip v_in
xmmp5 vy clk vdd_nom_123 vdd_nom_123 Switch_PMOS_n12_X1_Y1
xmmp4 vyy clk vdd_nom_123 vdd_nom_123 Switch_PMOS_n12_X1_Y1
xmmp3 vx clk vdd_nom_123 vdd_nom_123 Switch_PMOS_n12_X1_Y1
xmmp2 vxx clk vdd_nom_123 vdd_nom_123 Switch_PMOS_n12_X1_Y1
xmmn2 vcom clk vss vss Switch_NMOS_n12_X4_Y2
xmmp1_mmp0 vxx vyy vdd_nom_123 vdd_nom_123 CCP_PMOS_S_n12_X2_Y2
xmmn4_mmn3 vxx vyy vx vy vss CCP_NMOS_n12_X4_Y2
mmn5_mmp6 vxx vss vdd_nom_123 von INV_LVT
mmn6_mmp7 vyy vss vdd_nom_123 vop INV_LVT
xmmn1_mmn0 vy vip vcom vx v_in vss DP_NMOS_n12_X4_Y4
.ends high_speed_comparator

.subckt CCP_PMOS_S_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
.ends CCP_PMOS_S_n12_X2_Y2

.subckt CCP_NMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=96
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=96
.ends CCP_NMOS_n12_X4_Y2

.subckt DP_NMOS_n12_X4_Y4 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=192
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=192
.ends DP_NMOS_n12_X4_Y4
