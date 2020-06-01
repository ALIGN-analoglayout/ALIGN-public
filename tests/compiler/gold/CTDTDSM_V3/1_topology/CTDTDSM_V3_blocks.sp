
.subckt CTDTDSM_V3 avdd_sar avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk dout<3> dout<2> dout<1> dout<0> dvdd dvss mclk nsbsp<2> nsbsp<1> phsbuf vb_clk vb_samp veld yn vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> yp vcmi vrefn vrefp vsw ip xp in xn csel<2> csel<1> csel<0> ib_ota vcas vdd_int vrefnd vrefpd
xi58 avdd_sar avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk clkb d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> din dip dout<3> dout<2> dout<1> dout<0> dvdd dvss mclk net036 ns<2> ns<1> nsbsp<2> nsbsp<1> phsbuf net046<0> net046<1> net046<2> net046<3> sc<4> sc<3> sc<2> sc<1> vb_clk vb_samp veld yn vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> yp vcmi vrefn vrefp vsw NSSAR4B_wELD_V2A
xi60<2> dout<2> dvdd dvss net026<0> INVX4
xi60<1> dout<1> dvdd dvss net026<1> INVX4
xi60<0> dout<0> dvdd dvss net026<2> INVX4
xr7 xp ip Res_100
xr6 xn in Res_100
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

.subckt NSSAR4B_wELD_V2A avdd avss botep<3> botep<2> botep<1> botep<0> botp<3> botp<2> botp<1> botp<0> clk clkb d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> din dip dout<3> dout<2> dout<1> dout<0> f1 gt ns<2> ns<1> nsbs<2> nsbs<1> phsbuf s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> vb_clk vb_samp veld vin vintn<2> vintn<1> vintn<0> vintp<2> vintp<1> vintp<0> vip vref vrefn vrefp vsw
xi4<1> ns<2> avdd avss net011<0> INVX2
xi4<2> ns<1> avdd avss net011<1> INVX2
xi198 net07 avdd avss net06 INVX2
xi197<1> net011<0> avdd avss net012<0> INVX4
xi197<2> net011<1> avdd avss net012<1> INVX4
xi199 net06 avdd avss phs INVX4
xxm0 avss avdd avss Dcap_NMOS_n12_X1_Y1
xi177 clke dbn<3> dbn<2> dbn<1> dbn<0> dop<3> dop<2> dop<1> dop<0> don<3> don<2> don<1> don<0> dout<3> dout<2> dout<1> dout<0> dvdd dvss LOGIC_DOUT_V2
xi172 avdd avss botn<3> botn<2> botn<1> botn<0> boten<3> boten<2> boten<1> boten<0> d<3> db<2> db<1> db<0> deb<3> deb<2> deb<1> deb<0> net012<0> net012<1> net38<0> net38<1> phs veld vin vintn<2> vintn<1> vintn<0> vref vrefn vrefp net03 SC4B_wELD_V2
xi170 avdd avss botp<3> botp<2> botp<1> botp<0> botep<3> botep<2> botep<1> botep<0> db<3> d<2> d<1> d<0> de<3> de<2> de<1> de<0> net012<0> net012<1> nsbs<2> nsbs<1> phs veld vip vintp<2> vintp<1> vintp<0> vref vrefn vrefp vsw SC4B_wELD_V2
xi176 deb<3> deb<2> deb<1> deb<0> don<3> don<2> don<1> don<0> phe dvdd dvss LOGIC_ELD
xi173 de<3> de<2> de<1> de<0> dop<3> dop<2> dop<1> dop<0> phe dvdd dvss LOGIC_ELD
xi189 clk clkb din dip gt vb_clk avdd vintp<0> vintn<0> vintn<2> vintn<1> vintp<2> vintp<1> avss CLK_COMP
xxm1 avss avdd avdd Dcap_PMOS_n12_X1_Y1
xi206 avdd avss phs phsbuf net05 BUF248
xi174 clkb clke d<3> d<2> d<1> d<0> db<3> db<2> db<1> db<0> dbn<3> dbn<2> dbn<1> dbn<0> din dip dvdd dvss f1 gt ns<2> ns<1> phe net07 s<4> s<3> s<2> s<1> sc<4> sc<3> sc<2> sc<1> vb_samp NSSAR_LOGIC_ELD_V2
.ends NSSAR4B_wELD_V2A

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt INVX2 i vdd vss zn
xxm1 zn i vss vss Switch_NMOS_n12_X1_Y1
xxm0 zn i vdd vdd Switch_PMOS_n12_X1_Y1
.ends INVX2

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt INVX4 i vdd vss zn
xxm1 zn i vss vss Switch_NMOS_n12_X1_Y1
xxm0 zn i vdd vdd Switch_PMOS_n12_X1_Y1
.ends INVX4

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

.subckt DFF_TSPC_V2 clk d q
xxm20 net018 net09 dvss dvss Switch_NMOS_n12_X1_Y1
xxm19 net012 clk net018 dvss Switch_NMOS_n12_X1_Y1
xxm16 q net012 dvss dvss Switch_NMOS_n12_X1_Y1
xxm0 net13 d dvss dvss Switch_NMOS_n12_X1_Y1
xxm1 net019 clk dvss dvss Switch_NMOS_n12_X1_Y1
xxm10 net09 net13 net019 dvss Switch_NMOS_n12_X1_Y1
xxm17 q net012 dvdd dvdd Switch_PMOS_n12_X1_Y1
xxm18 net012 net09 dvdd dvdd Switch_PMOS_n12_X1_Y1
xxm4 net09 clk dvdd dvdd Switch_PMOS_n12_X1_Y1
xxm5 net7 d dvdd dvdd Switch_PMOS_n12_X1_Y1
xxm9 net13 clk net7 dvdd Switch_PMOS_n12_X1_Y1
.ends DFF_TSPC_V2

.subckt BUF22444 in out outb outbb
xi0 net21 dvdd dvss net07 INVX2
xi184 in dvdd dvss net21 INVX2
xi187 outb dvdd dvss out INVX4
xi185 net07 dvdd dvss outb INVX4
xi186 out dvdd dvss outbb INVX4
.ends BUF22444

.subckt SC4B_wELD_V2 avdd avss bot<3> bot<2> bot<1> bot<0> bote<3> bote<2> bote<1> bote<0> d<3> d<2> d<1> d<0> de<3> de<2> de<1> de<0> ns<2> ns<1> nsbs<2> nsbs<1> phs veld vin vint<2> vint<1> vint<0> vref vrefn vrefp vsw
xxm0 vint<0> nsbs<1> vint<1> avss Switch_NMOS_n12_X1_Y1
xxm1 vint<0> nsbs<2> vint<2> avss Switch_NMOS_n12_X1_Y1
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

.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt stage2_inv G1 SN G2 SP
MM0_MM2 D SN SP G1 INV_LVT
MM1_MM3 G2 SN SP D INV_LVT
.ends stage2_inv

.subckt BSSW_WOTOD avdd avss phi vg vin vout
xxm13 phie phieb avss avss Switch_NMOS_n12_X1_Y1
xxm5 net13 phieb net06 avss Switch_NMOS_n12_X1_Y1
xxm2 net13 vg net06 avss Switch_NMOS_n12_X1_Y1
xxm3 net016 avdd vg avss Switch_NMOS_n12_X1_Y1
xxm28 avss phie net016 avss Switch_NMOS_n12_X1_Y1
xxm24 net13 phie avss avss Switch_NMOS_n12_X1_Y1
xxm25 vout vg vin avss Switch_NMOS_n12_X1_Y1
xxm26 vin vg net13 avss Switch_NMOS_n12_X1_Y1
xxm12 phie phieb avdd avdd Switch_PMOS_n12_X1_Y1
xxm1 vg net06 net8 net8 Switch_PMOS_n12_X1_Y1
xxm4 net06 phieb avdd avdd Switch_PMOS_n12_X1_Y1
xxm0 net8 vg avdd net8 Switch_PMOS_n12_X1_Y1
xc0 net8 net13 Cap_10f
xm10_xm9_xm11_xm8 avss phi avdd phieb stage2_inv
.ends BSSW_WOTOD

.subckt BSSW_WOTOD_NS avdd avss phi vcm vg
xxm5 net019 phieb net018 avss Switch_NMOS_n12_X1_Y1
xxm3 net016 avdd vg avss Switch_NMOS_n12_X1_Y1
xxm28 avss phie net016 avss Switch_NMOS_n12_X1_Y1
xxm24 net019 phie avss avss Switch_NMOS_n12_X1_Y1
xxm7 vcm phieb net019 avss Switch_NMOS_n12_X1_Y1
xxm26 vcm vg net019 avss Switch_NMOS_n12_X1_Y1
xxm6 net018 phie net019 avdd Switch_PMOS_n12_X1_Y1
xxm1 vg net018 net8 net8 Switch_PMOS_n12_X1_Y1
xxm4 net018 phieb avdd avdd Switch_PMOS_n12_X1_Y1
xxm0 net8 phieb avdd net8 Switch_PMOS_n12_X1_Y1
xc0 net8 net019 Cap_10f
xm12_xm10_xm11_xm9 avss phi avdd phieb stage2_inv
.ends BSSW_WOTOD_NS
