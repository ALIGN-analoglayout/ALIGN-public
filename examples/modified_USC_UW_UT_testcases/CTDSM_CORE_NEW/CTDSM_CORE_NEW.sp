* label = ADC
.subckt Gm1_v5_Practice ibias vdd vim vip vom vop vss
m8 net074 ntail1 vss vss hvtnfet w=w0 l=l0
m2 vdd ibias vdd vdd lvtpfet w=w1 l=l1
m4 vdd ibias vdd vdd lvtpfet w=w1 l=l1
m12 ibias ibias vdd vdd lvtpfet w=w2 l=l0
m11 vom ibias vdd vdd lvtpfet w=w3 l=l0
m14 vop ibias vdd vdd lvtpfet w=w3 l=l0
m26 vop vim net074 net074 lvtnfet w=w4 l=l0
m27 vom vip net074 net074 lvtnfet w=w4 l=l0
c21 ntail1 vom 10f
c22 vop ntail1 10f
r12 ntail1 vop 100
r11 vom ntail1 100
m3 vss ntail1 vss vss lvtnfet w=w5 l=l2
m0 vss ntail1 vss vss lvtnfet w=w5 l=l2
**d0 net074 vdd diode
**d1 vss vdd diode
.ends Gm1_v5_Practice

.subckt DFCNQD2BWP d cp cdn q vdd vss
m0 net63 cp vss vss nfet w=w6 l=l3
mi4 net61 net63 vss vss nfet w=w7 l=l3
m1 net97 cdn net60 vss nfet w=w8 l=l3
m2 net123 net95 vss vss nfet w=w9 l=l3
mi29 net49 net63 net17 vss nfet w=w10 l=l3
mi15 net123 net81 net49 vss nfet w=w9 l=l3
m3 net60 net49 vss vss nfet w=w8 l=l3
m4 net97 cdn net21 vss nfet w=w8 l=l3
m5 net81 net63 vss vss nfet w=w6 l=l3
mi5 net95 d net61 vss nfet w=w7 l=l3
mi49 net25 cdn vss vss nfet w=w10 l=l3
m6 net21 net49 vss vss nfet w=w8 l=l3
mi26 net17 net97 vss vss nfet w=w10 l=l3
mi48 net13 net123 net25 vss nfet w=w10 l=l3
m7 q net97 vss vss nfet w=w7 l=l3
m8 q net97 vss vss nfet w=w7 l=l3
mi47 net95 net81 net13 vss nfet w=w10 l=l3
mi33 net80 net97 vdd vdd pfet w=w10 l=l3
m9 q net97 vdd vdd pfet w=w11 l=l3
m10 net97 net49 vdd vdd pfet w=w12 l=l3
mi43 net101 net123 vdd vdd pfet w=w10 l=l3
mi6 net95 d net120 vdd pfet w=w13 l=l3
m11 q net97 vdd vdd pfet w=w11 l=l3
m12 net97 net49 vdd vdd pfet w=w12 l=l3
m13 net97 cdn vdd vdd pfet w=w12 l=l3
mi44 net101 cdn vdd vdd pfet w=w10 l=l3
m14 net97 cdn vdd vdd pfet w=w12 l=l3
m15 net123 net95 vdd vdd pfet w=w14 l=l3
m16 net63 cp vdd vdd pfet w=w15 l=l3
mi16 net123 net63 net49 vdd pfet w=w14 l=l3
m17 net81 net63 vdd vdd pfet w=w15 l=l3
mi32 net49 net81 net80 vdd pfet w=w10 l=l3
mi45 net95 net63 net101 vdd pfet w=w10 l=l3
mi7 net120 net81 vdd vdd pfet w=w13 l=l3
.ends DFCNQD2BWP

.subckt C_DAC clkb in r3 r4 rstb vdd vss
r27 r3 net10 100
r64 r4 in 100
xi94 in clkb rstb net10 vdd vss DFCNQD2BWP
.ends C_DAC

.subckt FIR_DAC clk in r1 r2 rstb vdd vss
r19 r1 net3 100
r48 r2 in 100
xi86 in clk rstb net3 vdd vss DFCNQD2BWP
.ends FIR_DAC

.subckt C1 a b
c0<3> a b 10f
c0<2> a b 10f
c0<1> a b 10f
c0<0> a b 10f
.ends C1

.subckt NR2D8BWP a1 a2 zn vdd vss
m0 zn a2 vss vss nfet w=w16 l=l3
m1 zn a1 vss vss nfet w=w16 l=l3
m2 net13 a2 vdd vdd pfet w=w17 l=l3
m3 zn a1 net13 vdd pfet w=w17 l=l3
.ends NR2D8BWP

.subckt SR_Latch q qb r s vdd vss
xi1 r qb q vdd vss NR2D8BWP
xi0 s q qb vdd vss NR2D8BWP
.ends SR_Latch

.subckt Gm2_v5_Practice ibias vdd vim vip vom vop vss
m20 vdd ibias vdd vdd lvtpfet w=w18 l=l4
m18 vdd ibias vdd vdd lvtpfet w=w18 l=l4
m13 vop vim net100 net100 lvtnfet w=w19 l=l5
m21 vom vip net100 net100 lvtnfet w=w19 l=l5
m0 ibias ibias vdd vdd pfet w=w20 l=l5
m24 ibias ibias vdd vdd pfet w=w20 l=l5
m23 vop ibias vdd vdd pfet w=w21 l=l5
m14 vom ibias vdd vdd pfet w=w21 l=l5
c22 vop ntail2 10f
c21 ntail2 vom 10f
r11 vom ntail2 100
r12 ntail2 vop 100
m22 net100 ntail2 vss vss nfet w=w22 l=l5
*d1 vss vdd diode
m12 vss ntail2 vss vss lvtnfet w=w23 l=l2
m11 vss ntail2 vss vss lvtnfet w=w23 l=l2
*d0 net100 vdd diode
.ends Gm2_v5_Practice

.subckt myComparator_v3 clk vss outm outp vdd _net0 _net1
m0 vss intern vss vss lvtnfet w=w24 l=l6
m22 vss interp vss vss lvtnfet w=w24 l=l6
m16 outm crossp vss vss lvtnfet w=w25 l=l3
m17 outp crossn vss vss lvtnfet w=w25 l=l3
m4 crossn crossp intern vss lvtnfet w=w26 l=l3
m3 crossp crossn interp vss lvtnfet w=w26 l=l3
m7 net069 clk vss vss lvtnfet w=w27 l=l3
m5 intern _net0 net069 vss lvtnfet w=w28 l=l3
m6 interp _net1 net069 vss lvtnfet w=w28 l=l3
m8 outm crossp vdd vdd lvtpfet w=w26 l=l3
m18 intern clk vdd vdd lvtpfet w=w26 l=l3
m15 outp crossn vdd vdd lvtpfet w=w26 l=l3
m2 interp clk vdd vdd lvtpfet w=w26 l=l3
m1 crossn clk vdd vdd lvtpfet w=w26 l=l3
m12 crossp clk vdd vdd lvtpfet w=w26 l=l3
m14 crossn crossp vdd vdd lvtpfet w=w29 l=l3
m13 crossp crossn vdd vdd lvtpfet w=w29 l=l3
.ends myComparator_v3

.subckt FIR_DAC_schematic clk in r1 r2 rstb vdd vss
r19 r1 net3 100
r48 r2 in 100
xi86 in clk rstb net3 vdd vss DFCNQD2BWP
.ends FIR_DAC_schematic

.subckt C_DAC_schematic clkb in r3 r4 rstb vdd vss
r27 r3 net10 100
r64 r4 in 100
xi94 in clkb rstb net10 vdd vss DFCNQD2BWP
.ends C_DAC_schematic

.subckt CTDSM_CORE_NEW clk clkb1 clkb2 ibias1 ibias2 outm outp rstb vdd vim vip vss
xi160 ibias1 vdd vo1m vo1p vo2p vo2m vss Gm1_v5_Practice
xi154 clkb1 net062 vo3m vo3p rstb vdd vss FIR_DAC
xi152 clk net052 vo1p vo1p rstb vdd vss FIR_DAC
m1 vss clkb2 vss vss nfet w=w30 l=l7
m0 vss clkb1 vss vss nfet w=w30 l=l7
xi164 vo1p vo1m C1
xi128 outm outp net072 net071 vdd vss SR_Latch
c6 vo3p vo3m 10f
c3 net074 net073 10f
r16 vip vo1p 100
r51 net073 vo2m 100
r25 vo2p net074 100
r47 vim vo1m 100
xi161 ibias2 vdd vo2m vo2p vo3p vo3m vss Gm1_v5_Practice
xi88 net062 clk rstb net052 vdd vss DFCNQD2BWP
xi97 outp clkb1 rstb net062 vdd vss DFCNQD2BWP
xi92 net063 clk rstb net051 vdd vss DFCNQD2BWP
xi99 outm clkb2 rstb net063 vdd vss DFCNQD2BWP
xi146 clk vss net072 net071 vdd vo3p vo3m myComparator_v3
xi153 clk net051 vo1m vo1m rstb vdd vss FIR_DAC
xi155 clkb2 net063 vo3p vo3m rstb vdd vss FIR_DAC
.ends CTDSM_CORE_NEW

