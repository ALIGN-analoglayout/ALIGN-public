* label = ADC
.subckt INVX2 i vdd vss zn
m1 zn i vss vss lvtnfet w=w0 l=l0
m0 zn i vdd vdd lvtpfet w=w1 l=l0
.ends INVX2

.subckt INVX4 i vdd vss zn
m1 zn i vss vss lvtnfet w=w2 l=l0
m0 zn i vdd vdd lvtpfet w=w3 l=l0
.ends INVX4

.subckt DFF_TSPC_V2 clk d dvdd dvss q
m20 net018 net09 dvss dvss lvtnfet w=w0 l=l0
m19 net012 clk net018 dvss lvtnfet w=w0 l=l0
m16 q net012 dvss dvss lvtnfet w=w4 l=l0
m0 net13 d dvss dvss lvtnfet w=w4 l=l0
m1 net019 clk dvss dvss lvtnfet w=w0 l=l0
m10 net09 net13 net019 dvss lvtnfet w=w0 l=l0
m17 q net012 dvdd dvdd lvtpfet w=w0 l=l0
m18 net012 net09 dvdd dvdd lvtpfet w=w0 l=l0
m4 net09 clk dvdd dvdd lvtpfet w=w0 l=l0
m5 net7 d dvdd dvdd lvtpfet w=w0 l=l0
m9 net13 clk net7 dvdd lvtpfet w=w0 l=l0
.ends DFF_TSPC_V2

.subckt BUF22444 dvdd dvss in out outb outbb
xi0 net21 dvdd dvss net07 INVX2
xi184 in dvdd dvss net21 INVX2
xi187 outb dvdd dvss out INVX4
xi185 net07 dvdd dvss outb INVX4
xi186 out dvdd dvss outbb INVX4
.ends BUF22444

.subckt LOGIC_DOUT_V2 clk d<3> d<2> d<1> d<0> doe<3> doe<2> doe<1> doe<0> doeb<3> doeb<2> doeb<1> doeb<0> dout<3> dout<2> dout<1> dout<0> vdd vss
xi3 net10 vdd vss clkd INVX4
xi2 clk vdd vss net10 INVX2
xi1<3> clkd d<3> vdd vss dop<3> DFF_TSPC_V2
xi1<2> clkd d<2> vdd vss dop<2> DFF_TSPC_V2
xi1<1> clkd d<1> vdd vss dop<1> DFF_TSPC_V2
xi1<0> clkd d<0> vdd vss dop<0> DFF_TSPC_V2
xi18 vdd vss dop<3> doe<3> doeb<3> dout<3> BUF22444
xi36 vdd vss dop<0> doe<0> doeb<0> dout<0> BUF22444
xi35 vdd vss dop<1> doe<1> doeb<1> dout<1> BUF22444
xi34 vdd vss dop<2> doe<2> doeb<2> dout<2> BUF22444
.ends LOGIC_DOUT_V2

.subckt BSSW_WOTOD avdd avss phi vg vin vout
m13 phie phieb avss avss lvtnfet w=w5 l=l0
m10 phieb net013 avss avss lvtnfet w=w5 l=l0
m9 net013 phi avss avss lvtnfet w=w5 l=l0
m5 net13 phieb net06 avss lvtnfet w=w5 l=l0
m2 net13 vg net06 avss lvtnfet w=w5 l=l0
m3 net016 avdd vg avss lvtnfet w=w6 l=l0
m28 avss phie net016 avss lvtnfet w=w5 l=l0
m24 net13 phie avss avss lvtnfet w=w5 l=l0
m25 vout vg vin avss lvtnfet w=w7 l=l0
m26 vin vg net13 avss lvtnfet w=w5 l=l0
m12 phie phieb avdd avdd lvtpfet w=w6 l=l0
m11 phieb net013 avdd avdd lvtpfet w=w6 l=l0
m8 net013 phi avdd avdd lvtpfet w=w6 l=l0
m1 vg net06 net8 net8 lvtpfet w=w5 l=l0
m4 net06 phieb avdd avdd lvtpfet w=w5 l=l0
**need primitive m0 net8 vg avdd net8 lvtpfet w=w5 l=l0
c0 net8 net13 10f
.ends BSSW_WOTOD

.subckt BSSW_WOTOD_NS avdd avss phi vcm vg
m12 phieb phie avss avss lvtnfet w=w8 l=l0
m5 net019 phieb net018 avss lvtnfet w=w5 l=l0
m3 net016 avdd vg avss lvtnfet w=w5 l=l0
m10 phie phi avss avss lvtnfet w=w8 l=l0
m28 avss phie net016 avss lvtnfet w=w5 l=l0
m24 net019 phie avss avss lvtnfet w=w5 l=l0
m7 vcm phieb net019 avss lvtnfet w=w5 l=l0
m26 vcm vg net019 avss lvtnfet w=w5 l=l0
m11 phieb phie avdd avdd lvtpfet w=w5 l=l0
m9 phie phi avdd avdd lvtpfet w=w5 l=l0
m6 net018 phie net019 avdd lvtpfet w=w5 l=l0
m1 vg net018 net8 net8 lvtpfet w=w6 l=l0
m4 net018 phieb avdd avdd lvtpfet w=w5 l=l0
**need primitive m0 net8 phieb avdd net8 lvtpfet w=w5 l=l0
c0 net8 net019 10f
.ends BSSW_WOTOD_NS

.subckt INVX1NB i vb vdd vss zn
m1 zn i vss vb lvtnfet w=w9 l=l0
m0 zn i vdd vdd lvtpfet w=w8 l=l0
.ends INVX1NB

.subckt INVX8NB i vb vdd vss zn
m1 zn i vss vb lvtnfet w=w6 l=l0
m0 zn i vdd vdd lvtpfet w=w7 l=l0
.ends INVX8NB

.subckt INVX2NB i vb vdd vss zn
m1 zn i vss vb lvtnfet w=w8 l=l0
m0 zn i vdd vdd lvtpfet w=w5 l=l0
.ends INVX2NB

.subckt INVX4NB i vb vdd vss zn
m1 zn i vss vb lvtnfet w=w5 l=l0
m0 zn i vdd vdd lvtpfet w=w6 l=l0
.ends INVX4NB

.subckt SC4B_wELD_V2 avdd avss bot<3> bot<2> bot<1> bot<0> bote<3> bote<2> bote<1> bote<0> d<3> d<2> d<1> d<0> de<3> de<2> de<1> de<0> ns<2> ns<1> nsbs<2> nsbs<1> phs veld vin vint<2> vint<1> vint<0> vref vrefn vrefp vsw
m0 vint<0> nsbs<1> vint<1> avss lvtnfet w=w10 l=l0
m1 vint<0> nsbs<2> vint<2> avss lvtnfet w=w10 l=l0
xi159 avdd avss phs vsw vin vint<0> BSSW_WOTOD
xi2<2> avdd avss ns<2> vref nsbs<2> BSSW_WOTOD_NS
xi2<1> avdd avss ns<1> vref nsbs<1> BSSW_WOTOD_NS
xi151 de<0> avss veld vrefn bote<0> INVX1NB
xi164 d<1> avss vrefp vrefn bot<1> INVX1NB
xi165 d<1> avss vrefp vrefn botb<1> INVX1NB
xi167 d<0> avss vrefp vrefn bot<0> INVX1NB
xi150 de<3> avss veld vrefn bote<3> INVX8NB
xi153 de<1> avss veld vrefn bote<1> INVX2NB
xi162 d<2> avss vrefp vrefn bot<2> INVX2NB
xi163 d<2> avss vrefp vrefn botb<2> INVX2NB
xi152 de<2> avss veld vrefn bote<2> INVX4NB
xi170 d<3> avss vrefp vrefn net4 INVX4NB
xi169 net4 avss vrefp vrefn bot<3> INVX4NB
xi161 net4 avss vrefp vrefn botb<3> INVX4NB
.ends SC4B_wELD_V2

.subckt INVX1 i vdd vss zn
m1 zn i vss vss lvtnfet w=w4 l=l0
m0 zn i vdd vdd lvtpfet w=w11 l=l0
.ends INVX1

.subckt nor a b dvdd dvss o
m1 o b net8 dvdd lvtpfet w=w1 l=l0
m5 net8 a dvdd dvdd lvtpfet w=w1 l=l0
m0 o b dvss dvss lvtnfet w=w4 l=l0
m3 o a dvss dvss lvtnfet w=w4 l=l0
.ends nor

.subckt NANDX2 a b dvdd dvss o
m13 o b dvdd dvdd lvtpfet w=w1 l=l0
m1 o a dvdd dvdd lvtpfet w=w1 l=l0
m6 net011 b dvss dvss lvtnfet w=w0 l=l0
m0 o a net011 dvss lvtnfet w=w0 l=l0
.ends NANDX2

.subckt LOGIC_ELD de<3> de<2> de<1> de<0> do<3> do<2> do<1> do<0> phe vdd vss
xi12 net03 vdd vss de<3> INVX4
xi17 net014 vdd vss de<1> INVX1
xi19 net013 vdd vss de<0> INVX1
xi15 net015 vdd vss de<2> INVX2
xi11 sampd vss vdd vss sampb INVX2NB
xi158 phe vss vdd vss sampd INVX2NB
xi134 sampb do<3> vdd vss net03 nor
xi16 do<1> sampd vdd vss net014 nor
xi14 do<2> sampd vdd vss net015 NANDX2
xi18 do<0> sampd vdd vss net013 NANDX2
.ends LOGIC_ELD

.subckt CLK_COMP clk clkbo dn dp gt vb vdd vin vinb vintn<2> vintn<1> vintp<2> vintp<1> vss
m103 clkb clk vdd vdd lvtpfet w=w5 l=l0
m30 clk net030 vdd vdd lvtpfet w=w12 l=l0
m124 clkbo clk vdd vdd lvtpfet w=w5 l=l0
m16 v2p vxn vdd _net0 lvtpfet w=w13 l=l0
m114 d v2n vdd vdd lvtpfet w=w7 l=l0
m122 dp db vdd vdd lvtpfet w=w6 l=l0
m25 vmid v2p vdd vdd lvtpfet w=w6 l=l0
m14 net027 d vdd vdd lvtpfet w=w5 l=l0
m24 db v2p vdd vdd lvtpfet w=w7 l=l0
m85 net030 gt vdd vdd lvtpfet w=w7 l=l0
m6 net031 net027 vdd vdd lvtpfet w=w6 l=l0
m8 db d vdd vdd lvtpfet w=w7 l=l0
m5 d db vdd vdd lvtpfet w=w7 l=l0
m119 dn d vdd vdd lvtpfet w=w6 l=l0
m71 net027 db vdd vdd lvtpfet w=w5 l=l0
m9 net030 net031 vdd vdd lvtpfet w=w7 l=l0
m35 vxn clk vdd vdd lvtpfet w=w13 l=l0
m73 vxp clk vdd vdd lvtpfet w=w13 l=l0
m19 v2n vxp vdd _net0 lvtpfet w=w13 l=l0
m26 vmidb v2n vdd vdd lvtpfet w=w6 l=l0
m10 net030 net031 net032 vss lvtnfet w=w7 l=l0
m69 v1p vintn<1> vss vss lvtnfet w=w14 l=l0
m17 net032 gt vss vss lvtnfet w=w7 l=l0
m116 vxp clk v1p vss lvtnfet w=w7 l=l0
m102 clkb clk vss vss lvtnfet w=w8 l=l0
m120 dn d vss vss lvtnfet w=w5 l=l0
m1 db d vmid vss lvtnfet w=w7 l=l0
m113 vmidb v2n vss vss lvtnfet w=w7 l=l0
m7 net031 net027 vss vss lvtnfet w=w5 l=l0
**need primitive m28 vss vss v1p vss lvtnfet w=w8 l=l0
m70 v1p vinb vss vss lvtnfet w=w8 l=l0
m97 net027 clkb net0107 vss lvtnfet w=w5 l=l0
m12 net0107 vb vss vss lvtnfet w=w7 l=l0
m121 dp db vss vss lvtnfet w=w5 l=l0
m115 vxn clk v1n vss lvtnfet w=w7 l=l0
m27 clk net030 vss vss lvtnfet w=w7 l=l0
m20 v2p vxn vss vss lvtnfet w=w7 l=l0
m3 d db vmidb vss lvtnfet w=w7 l=l0
m18 vss vss vss vss lvtnfet w=w8 l=l0
m55 v1n vin vss vss lvtnfet w=w8 l=l0
**need primitive m23 vss vss v1n vss lvtnfet w=w8 l=l0
m57 v1n vintp<2> vss vss lvtnfet w=w13 l=l0
m125 clkbo clk vss vss lvtnfet w=w8 l=l0
m22 vmid v2p vss vss lvtnfet w=w7 l=l0
m21 v2n vxp vss vss lvtnfet w=w7 l=l0
m56 v1n vintp<1> vss vss lvtnfet w=w14 l=l0
m68 v1p vintn<2> vss vss lvtnfet w=w13 l=l0
.ends CLK_COMP

.subckt INVX8 i vdd vss zn
m1 zn i vss vss lvtnfet w=w15 l=l0
m0 zn i vdd vdd lvtpfet w=w16 l=l0
.ends INVX8

.subckt BUF248 dvdd dvss in out outa
xi186 net23 dvdd dvss out INVX8
xi184 in dvdd dvss net21 INVX1
xi185 net21 dvdd dvss outa INVX2
xi187 outa dvdd dvss net23 INVX4
.ends BUF248

.subckt GT_GEN dvdd dvss gt last start
xi319 net028 dvdd dvss net027 INVX2
m12 b a net030 dvdd lvtpfet w=w8 l=l0
m1 net030 last dvdd dvdd lvtpfet w=w8 l=l0
m4 c b dvdd dvdd lvtpfet w=w5 l=l0
xi3 net016 dvdd dvss net021 INVX1
xi2 net021 dvdd dvss net028 INVX1
xi1 start dvdd dvss net014 INVX1
xi252 c dvdd dvss net016 INVX1
xi0 net014 dvdd dvss a INVX1
xi320 net027 dvdd dvss gt INVX4
m2 b last dvss dvss lvtnfet w=w8 l=l0
m9 net029 b dvss dvss lvtnfet w=w8 l=l0
m13 c a net029 dvss lvtnfet w=w8 l=l0
.ends GT_GEN

.subckt AND2 dvdd dvss s1 s2 sc
m12 sc net017 dvss dvss lvtnfet w=w4 l=l0
m6 net011 s2 dvss dvss lvtnfet w=w4 l=l0
m0 net017 s1 net011 dvss lvtnfet w=w4 l=l0
m13 net017 s2 dvdd dvdd lvtpfet w=w11 l=l0
m11 sc net017 dvdd dvdd lvtpfet w=w11 l=l0
m1 net017 s1 dvdd dvdd lvtpfet w=w11 l=l0
.ends AND2

.subckt NS2_GEN dvdd dvss ns<2> start stop
xi282 net021 dvdd dvss ns<2> INVX2
xi283 net022 dvdd dvss net021 INVX1
xi333 dvdd dvss start stop net022 AND2
.ends NS2_GEN

.subckt DELAY_VAR_V2 i o vb vdd vss
m13 net017 net021 vdd vdd lvtpfet w=w8 l=l1
m11 net021 net019 vdd vdd lvtpfet w=w8 l=l1
m10 net011 net015 vdd vdd lvtpfet w=w8 l=l2
m6 o net017 vdd vdd lvtpfet w=w5 l=l0
m0 net019 net011 vdd vdd lvtpfet w=w8 l=l1
m2 net015 i vdd vdd lvtpfet w=w8 l=l2
m12 net017 net021 vss vss lvtnfet w=w9 l=l1
m8 net021 net019 vss vss lvtnfet w=w9 l=l1
m9 net011 net015 net016 vss lvtnfet w=w8 l=l2
m7 net016 vb vss vss lvtnfet w=w8 l=l2
m5 o net017 vss vss lvtnfet w=w8 l=l0
m4 net019 net011 vss vss lvtnfet w=w9 l=l1
m1 net015 i net8 vss lvtnfet w=w8 l=l2
m3 net8 vb vss vss lvtnfet w=w8 l=l2
.ends DELAY_VAR_V2

.subckt PHS_DELAY_V2 dvdd dvss f1 sd1 sd2 vb
xi3 net011 net010 vb dvdd dvss DELAY_VAR_V2
xi4 net010 sd2 vb dvdd dvss DELAY_VAR_V2
xi0 f1 dvdd dvss net05 INVX2
xi2 sd1 dvdd dvss net011 INVX2
xi1 net05 dvdd dvss sd1 INVX4
.ends PHS_DELAY_V2

.subckt INVX6 i vdd vss zn
m1 zn i vss vss lvtnfet w=w17 l=l0
m0 zn i vdd vdd lvtpfet w=w15 l=l0
.ends INVX6

.subckt NAND2 a b dvdd dvss o
m6 net011 b dvss dvss lvtnfet w=w4 l=l0
m0 o a net011 dvss lvtnfet w=w4 l=l0
m13 o b dvdd dvdd lvtpfet w=w11 l=l0
m1 o a dvdd dvdd lvtpfet w=w11 l=l0
.ends NAND2

.subckt CLK_NONOVERLAP dvdd dvss in out outb
xi14 net012 dvdd dvss net013 INVX2
xi16 net011 dvdd dvss net09 INVX2
xi17 net013 dvdd dvss outb INVX4
xi18 net09 dvdd dvss out INVX4
xi11 net016 in dvdd dvss net018 NAND2
xi8 net031 net018 dvdd dvss net016 NAND2
xi12 net016 dvdd dvss net012 INVX1
xi19 in dvdd dvss net031 INVX1
xi15 net018 dvdd dvss net011 INVX1
.ends CLK_NONOVERLAP

.subckt PHS_GEN_V2 dvdd dvss phe sd1 sd2 st
xi4 net06 dvdd dvss phe INVX6
xi250 sd1 sd2 dvdd dvss net029 nor
xi334 dvdd dvss net029 st net06 CLK_NONOVERLAP
.ends PHS_GEN_V2

.subckt DFF_TSPCn_SC_v2 clk d dvdd dvss q sc
m26 clkb clk dvss dvss lvtnfet w=w9 l=l0
m22 q clkb net048 dvss lvtnfet w=w1 l=l0
m18 b d dvss dvss lvtnfet w=w4 l=l0
m3 net048 b dvss dvss lvtnfet w=w1 l=l0
m20 sc net044 dvss dvss lvtnfet w=w0 l=l0
m19 net044 q net047 dvss lvtnfet w=w0 l=l0
m14 s2b d dvss dvss lvtnfet w=w9 l=l0
m16 net047 s2b dvss dvss lvtnfet w=w0 l=l0
m29 clkb clk dvdd dvdd lvtpfet w=w8 l=l0
m28 net049 d dvdd dvdd lvtpfet w=w0 l=l0
m27 q b dvdd dvdd lvtpfet w=w0 l=l0
m21 b clkb net049 dvdd lvtpfet w=w0 l=l0
m25 net044 s2b dvdd dvdd lvtpfet w=w0 l=l0
m24 sc net044 dvdd dvdd lvtpfet w=w2 l=l0
m23 net044 q dvdd dvdd lvtpfet w=w0 l=l0
m17 s2b d dvdd dvdd lvtpfet w=w8 l=l0
.ends DFF_TSPCn_SC_v2

.subckt INVMINI i vdd vss zn
m1 zn i vss vss lvtnfet w=w9 l=l0
m0 zn i vdd vdd lvtpfet w=w18 l=l0
.ends INVMINI

.subckt INV i vdd vss zn
m1 zn i vss vss lvtnfet w=w4 l=l0
m0 zn i vdd vdd lvtpfet w=w11 l=l0
.ends INV

.subckt TG cn cp dvdd dvss vin vout
m11 vin cn vout dvdd lvtpfet w=w0 l=l0
m9 vout cp vin dvss lvtnfet w=w4 l=l0
.ends TG

.subckt Latch_D_new_V1 d db dvdd dvss q qb qbn rst sc
m2 net015 net021 dvdd dvdd lvtpfet w=w11 l=l0
m10 qb net021 dvdd dvdd lvtpfet w=w2 l=l0
m7 net021 rst dvdd dvdd lvtpfet w=w1 l=l0
m13 q net015 dvdd dvdd lvtpfet w=w2 l=l0
m1 net021 net015 dvdd dvdd lvtpfet w=w11 l=l0
m6 net015 rst dvdd dvdd lvtpfet w=w1 l=l0
xi24 sc dvdd dvss net037 INVMINI
xi16 sc dvdd dvss net022 INVMINI
xi23 net037 dvdd dvss net027 INVMINI
xi18 net022 dvdd dvss net032 INVMINI
m3 net021 sc net030 dvss lvtnfet w=w1 l=l0
m4 net028 d dvss dvss lvtnfet w=w2 l=l0
m5 net015 sc net028 dvss lvtnfet w=w1 l=l0
m0 net030 db dvss dvss lvtnfet w=w2 l=l0
m12 q net015 dvss dvss lvtnfet w=w0 l=l0
m9 qb net021 dvss dvss lvtnfet w=w0 l=l0
xi20 qb dvdd dvss net034 INV
xi25 q dvdd dvss qbn INV
xi11 net032 net022 dvdd dvss net021 net034 TG
xi26 net027 net037 dvdd dvss net015 qbn TG
.ends Latch_D_new_V1

.subckt SEQUENCER_V4 clk d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> dbn<3> dbn<2> dbn<1> dbn<0> din dip drst dvdd dvss s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> st
xi4<3> clk st dvdd dvss s<4> sc<4> DFF_TSPCn_SC_v2
xi4<2> clk s<4> dvdd dvss s<3> sc<3> DFF_TSPCn_SC_v2
xi4<1> clk s<3> dvdd dvss s<2> sc<2> DFF_TSPCn_SC_v2
xi4<0> clk s<2> dvdd dvss s<1> sc<1> DFF_TSPCn_SC_v2
xi3<4> dip din dvdd dvss d<3> db<3> dbn<3> drst sc<4> Latch_D_new_V1
xi3<3> dip din dvdd dvss d<2> db<2> dbn<2> drst sc<3> Latch_D_new_V1
xi3<2> dip din dvdd dvss d<1> db<1> dbn<1> drst sc<2> Latch_D_new_V1
xi3<1> dip din dvdd dvss d<0> db<0> dbn<0> drst sc<1> Latch_D_new_V1
.ends SEQUENCER_V4

.subckt NSSAR_LOGIC_ELD_V2 clk clke d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> dbn<3> dbn<2> dbn<1> dbn<0> din dip dvdd dvss f1 gt ns<2> ns<1> phe phs s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> vb
xi372 sd1 dvdd dvss net020 INVX1
xi377 dvss dvss dvss net037 INVX1
xi373 net020 dvdd dvss net023 INVX1
xi379 dvss dvss dvss net038 INVX1
xi355 dvdd dvss gt ns<1> phe GT_GEN
xi354 dvdd dvss ns<2> net019 net023 NS2_GEN
xi374 dvss dvss net035 dvss dvss NS2_GEN
xi381 dvss dvss net036 dvss dvss NS2_GEN
m2 net011 clk dvss dvss lvtnfet w=w19 l=l0
xi376 net037 dvss dvss net039 INVX2
xi380 net038 dvss dvss net046 INVX2
xi371 st dvdd dvss net018 INVX2
xi352 s<1> dvdd dvss net019 INVX2
xi364 net019 dvdd dvss net017 INVX2
xi346 sc<1> dvdd dvss net025 INVX2
xi357 dvdd dvss f1 sd1 sd2 vb PHS_DELAY_V2
xi369 net022 dvdd dvss phe INVX8
xi358 dvdd dvss net022 sd1 sd2 st PHS_GEN_V2
m3 net011 clk dvdd dvdd lvtpfet w=w14 l=l0
xi345 net011 d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> dbn<3> dbn<2> dbn<1> dbn<0> din dip phe dvdd dvss s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> st SEQUENCER_V4
xi365 net017 dvdd dvss clke INVX4
xi378 net039 dvss dvss net047 INVX4
xi370 net018 dvdd dvss phs INVX4
xi347 net025 dvdd dvss ns<1> INVX4
.ends NSSAR_LOGIC_ELD_V2

.subckt NSSAR4B_wELD_V2A avdd avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk clkb d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> din dip dout<3> dout<2> dout<1> dout<0> dvdd dvss f1 gt ns<2> ns<1> nsbs<2> nsbs<1> phsbuf s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> vb_clk vb_samp veld vin vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> vip vref vrefn vrefp vsw
xi4<1> ns<2> avdd avss net011<0> INVX2
xi4<2> ns<1> avdd avss net011<1> INVX2
xi198 net07 avdd avss net06 INVX2
xi197<1> net011<0> avdd avss net012<0> INVX4
xi197<2> net011<1> avdd avss net012<1> INVX4
xi199 net06 avdd avss phs INVX4
m0 avss avdd avss avss lvtnfet w=w20 l=l0
xi177 clke dbn<3> dbn<2> dbn<1> dbn<0> dop<3> dop<2> dop<1> dop<0> don<3> don<2> don<1> don<0> dout<3> dout<2> dout<1> dout<0> dvdd dvss LOGIC_DOUT_V2
xi172 avdd avss botn<3> botn<2> botn<1> botn<0> boten<3> boten<2> boten<1> boten<0> d<3> db<2> db<1> db<0> deb<3> deb<2> deb<1> deb<0> net012<0> net012<1> net38<0> net38<1> phs veld vin vintn<2> vintn<1> vintn<0> vref vrefn vrefp net03 SC4B_wELD_V2
xi170 avdd avss botp<3> botp<2> botp<1> botp<0> botep<3> botep<2> botep<1> botep<0> db<3> d<2> d<1> d<0> de<3> de<2> de<1> de<0> net012<0> net012<1> nsbs<2> nsbs<1> phs veld vip vintp<2> vintp<1> vintp<0> vref vrefn vrefp vsw SC4B_wELD_V2
xi176 deb<3> deb<2> deb<1> deb<0> don<3> don<2> don<1> don<0> phe dvdd dvss LOGIC_ELD
xi173 de<3> de<2> de<1> de<0> dop<3> dop<2> dop<1> dop<0> phe dvdd dvss LOGIC_ELD
xi189 clk clkb din dip gt vb_clk avdd vintp<0> vintn<0> vintn<2> vintn<1> vintp<2> vintp<1> avss CLK_COMP
**need primitive m1 avss avdd avss avdd lvtpfet w=w21 l=l0
xi206 avdd avss phs phsbuf net05 BUF248
xi174 clkb clke d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> dbn<3> dbn<2> dbn<1> dbn<0> din dip dvdd dvss f1 gt ns<2> ns<1> phe net07 s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> vb_samp NSSAR_LOGIC_ELD_V2
.ends NSSAR4B_wELD_V2A

.subckt OTA_FF_2s_v3 avdd avss ibin in ip on op vcas vcmi
m35 net057 ibin avdd avdd lvtpfet w=w22 l=l2
m34 cmfb vcmo net057 net057 lvtpfet w=w23 l=l2
m33 net044 vcmi net057 net057 lvtpfet w=w23 l=l2
m62 avdd ibin avdd avdd lvtpfet w=w24 l=l2
m54 net59 net59 net59 net59 lvtpfet w=w25 l=l2
m43 net5 net5 net5 net5 lvtpfet w=w25 l=l2
m53 avdd ibin avdd avdd lvtpfet w=w25 l=l2
m57 avdd ibin avdd avdd lvtpfet w=w24 l=l2
m37 op in net59 net59 lvtpfet w=w26 l=l2
m23 on ip net59 net59 lvtpfet w=w26 l=l2
m63 net75 vcas net75 net75 lvtpfet w=w24 l=l2
m58 net057 vcmo net057 net057 lvtpfet w=w23 l=l2
m36 net59 ibin avdd avdd lvtpfet w=w27 l=l2
m41 avdd ibin avdd avdd lvtpfet w=w25 l=l2
m16 ibin vcas net75 net75 lvtpfet w=w22 l=l2
m50 on1 ip net5 net5 lvtpfet w=w22 l=l2
m48 net057 vcmi net057 net057 lvtpfet w=w25 l=l2
m6 net75 ibin avdd avdd lvtpfet w=w22 l=l2
m4 net5 ibin avdd avdd lvtpfet w=w24 l=l2
m20 op1 in net5 net5 lvtpfet w=w22 l=l2
m11 avss on1 avss avss lvtnfet w=w22 l=l3
m10 avss op1 avss avss lvtnfet w=w22 l=l3
m1 avss avss avss avss lvtnfet w=w28 l=l2
m0 avss cmfb avss avss lvtnfet w=w28 l=l2
m66 avss on1 avss avss lvtnfet w=w29 l=l2
m64 avss op1 avss avss lvtnfet w=w29 l=l2
m55 avss avss avss avss lvtnfet w=w29 l=l2
m21 on op1 avss avss lvtnfet w=w28 l=l2
m19 op on1 avss avss lvtnfet w=w28 l=l2
m29 cmfb cmfb avss avss lvtnfet w=w30 l=l2
m14 op1 cmfb avss avss lvtnfet w=w29 l=l2
m13 on1 cmfb avss avss lvtnfet w=w29 l=l2
m59 avss net044 avss avss lvtnfet w=w29 l=l2
m30 net044 net044 avss avss lvtnfet w=w30 l=l2
m56 avss cmfb avss avss lvtnfet w=w29 l=l2
c4 on vcmo 10f
c5 op vcmo 10f
r12 vcmo op 100
r13 on vcmo 100
.ends OTA_FF_2s_v3

.subckt INT_V3 cs<2> cs<1> cs<0> c_sel<2> c_sel<1> c_sel<0> ib vcas vcmi vdd _net0 _net1 _net3 _net2 vss
m8 net035 c_sel<0> _net0 vss lvtnfet w=w29 l=l0
m7 net028 c_sel<1> _net0 vss lvtnfet w=w23 l=l0
m6 net037 c_sel<2> _net0 vss lvtnfet w=w22 l=l0
m2 cs<0> c_sel<0> _net1 vss lvtnfet w=w29 l=l0
m1 cs<1> c_sel<1> _net1 vss lvtnfet w=w23 l=l0
m0 cs<2> c_sel<2> _net1 vss lvtnfet w=w22 l=l0
xi181 vdd vss ib _net1 _net0 _net2 _net3 vcas vcmi OTA_FF_2s_v3
c11 vdd vss 10f
c6 cs<0> _net3 10f
c5 cs<1> _net3 10f
c1 cs<2> _net3 10f
c0 _net1 _net3 10f
c10 _net0 _net2 10f
c9 net028 _net2 10f
c8 net035 _net2 10f
c7 net037 _net2 10f
.ends INT_V3

.subckt INVX12 i vdd vss zn
m1 zn i vss vss lvtnfet w=w31 l=l0
m0 zn i vdd vdd lvtpfet w=w32 l=l0
.ends INVX12

.subckt Retiming_Latch_common clkb d do dob vdd_d vss_d
m39 net025 net017 vdd_d vdd_d lvtpfet w=w5 l=l0
m31 clk clkb vdd_d vdd_d lvtpfet w=w5 l=l0
m33 vdd_d vss_d vdd_d vdd_d lvtpfet w=w5 l=l0
m16 do dob vdd_d vdd_d lvtpfet w=w33 l=l0
m26 clkn clk vdd_d vdd_d lvtpfet w=w5 l=l0
m12 dob do vdd_d vdd_d lvtpfet w=w33 l=l0
m1 do clkn net36 vdd_d lvtpfet w=w34 l=l0
m0 net36 net025 vdd_d vdd_d lvtpfet w=w34 l=l0
m11 dob clkn net39 vdd_d lvtpfet w=w34 l=l0
m10 net39 net017 vdd_d vdd_d lvtpfet w=w34 l=l0
m37 net017 d vdd_d vdd_d lvtpfet w=w5 l=l0
m35 vdd_d vss_d vdd_d vdd_d lvtpfet w=w5 l=l0
m38 net025 net017 vss_d vss_d lvtnfet w=w33 l=l0
m30 clk clkb vss_d vss_d lvtnfet w=w8 l=l0
m17 do clk net37 vss_d lvtnfet w=w33 l=l0
m27 clkn clk vss_d vss_d lvtnfet w=w8 l=l0
m13 dob clk net38 vss_d lvtnfet w=w33 l=l0
m36 net017 d vss_d vss_d lvtnfet w=w33 l=l0
m21 dob do vss_d vss_d lvtnfet w=w18 l=l0
m20 do dob vss_d vss_d lvtnfet w=w18 l=l0
m19 net38 net017 vss_d vss_d lvtnfet w=w33 l=l0
**need primitive m34 vdd_d vss_d vdd_d vss_d lvtnfet w=w33 l=l0
m18 net37 net025 vss_d vss_d lvtnfet w=w33 l=l0
.ends Retiming_Latch_common

.subckt DAC dn dp ion iop vrefn vrefp vss_dac
m11 net09 dn vrefn vss_dac lvtnfet w=w35 l=l0
m7 net016 dp vrefn vss_dac lvtnfet w=w35 l=l0
m1 net018 net016 vrefn vss_dac lvtnfet w=w36 l=l0
m0 net010 net09 vrefn vss_dac lvtnfet w=w36 l=l0
m10 net016 dp vrefp vrefp lvtpfet w=w37 l=l0
m3 net018 net016 vrefp vrefp lvtpfet w=w38 l=l0
m2 net010 net09 vrefp vrefp lvtpfet w=w38 l=l0
m12 net09 dn vrefp vrefp lvtpfet w=w37 l=l0
r2 iop net018 100
r0 net010 ion 100
.ends DAC

.subckt Retiming_DAC clkb d ion iop vdd vrefn vrefp vss
xi0 clkb d net2 net1 vdd vss Retiming_Latch_common
xi1 net1 net2 ion iop vrefn vrefp vss DAC
.ends Retiming_DAC

.subckt CTDTDSM_V3 avdd_sar avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk csel<2> csel<1> csel<0> dout<3> dout<2> dout<1> dout<0> dvdd dvss ib_ota in ip mclk nsbsp<2> nsbsp<1> phsbuf vb_clk vb_samp vcas vcmi vdd_int veld vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> vrefn vrefnd vrefp vrefpd vsw xn xp yn yp
xi58 avdd_sar avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk clkb d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> din dip dout<3> dout<2> dout<1> dout<0> dvdd dvss mclk net036 ns<2> ns<1> nsbsp<2> nsbsp<1> phsbuf net046<0> net046<1> net046<2> net046<3> sc<4> sc<3> sc<2> sc<1> vb_clk vb_samp veld yn vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> yp vcmi vrefn vrefp vsw NSSAR4B_wELD_V2A
xi60<2> dout<2> dvdd dvss net026<0> INVX4
xi60<1> dout<1> dvdd dvss net026<1> INVX4
xi60<0> dout<0> dvdd dvss net026<2> INVX4
r7 ip xp 100
r6 in xn 100
xi39 net043<0> net043<1> net043<2> csel<2> csel<1> csel<0> ib_ota vcas vcmi vdd_int xn xp yp yn avss INT_V3
xi54 net015 dvdd dvss doutl<3> INVX12
xi53 phsbuf avdd_sar avss net045 INVX12
xi56<2> net026<0> dvdd dvss doutl<2> INVX8
xi56<1> net026<1> dvdd dvss doutl<1> INVX8
xi56<0> net026<2> dvdd dvss doutl<0> INVX8
xi59 dout<3> dvdd dvss net015 INVX6
xi7<15> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<14> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<13> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<12> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<11> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<10> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<9> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<8> net045 doutl<3> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<7> net045 doutl<2> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<6> net045 doutl<2> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<5> net045 doutl<2> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<4> net045 doutl<2> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<3> net045 doutl<1> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<2> net045 doutl<1> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
xi7<1> net045 doutl<0> xp xn dvdd vrefnd vrefpd dvss Retiming_DAC
.ends CTDTDSM_V3

