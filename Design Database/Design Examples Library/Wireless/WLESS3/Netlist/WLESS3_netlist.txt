
// Library name: PhasedArray_WB_V2
// Cell name: res_24K
// View name: schematic
subckt res_24K t1 t2 vss
    R4 (t2 net05 vss) rppolywo_rf l=8u w=500n m=1 mismatchflag=0
    R2 (net06 net05 vss) rppolywo_rf l=8u w=500n m=1 mismatchflag=0
    R1 (net06 net6 vss) rppolywo_rf l=8u w=500n m=1 mismatchflag=0
    R0 (t1 net6 vss) rppolywo_rf l=8u w=500n m=1 mismatchflag=0
ends res_24K
// End of subcircuit definition.

// Library name: PhasedArray_WB_V2
// Cell name: capbank_gp_lowC_noLSB_BPF
// View name: schematic
subckt capbank_gp_lowC_noLSB_BPF B\<3\> B\<2\> B\<1\> B\<0\> LEFT RIGHT \
        VDD VSS
    C5 (RIGHT net07 VSS) mimcap_woum_sin_rf lt=10u wt=10u lay=7 m=1 \
        mimflag=3 mismatchflag=0
    C4 (LEFT net010 VSS) mimcap_woum_sin_rf lt=10u wt=10u lay=7 m=1 \
        mimflag=3 mismatchflag=0
    C3 (RIGHT net3 VSS) mimcap_woum_sin_rf lt=5u wt=5u lay=7 m=2 mimflag=3 \
        mismatchflag=0
    C2 (LEFT net1 VSS) mimcap_woum_sin_rf lt=5u wt=5u lay=7 m=2 mimflag=3 \
        mismatchflag=0
    C1 (RIGHT net4 VSS) mimcap_woum_sin_rf lt=5u wt=5u lay=7 m=1 mimflag=3 \
        mismatchflag=0
    C0 (LEFT net2 VSS) mimcap_woum_sin_rf lt=5u wt=5u lay=7 m=1 mimflag=3 \
        mismatchflag=0
    M2 (net010 b2_buf net07 VSS) nmos_rf lr=60n wr=2u nr=20 sigma=1 m=5 \
        mismatchflag=0
    M1 (net1 b1_buf net3 VSS) nmos_rf lr=60n wr=2u nr=20 sigma=1 m=2 \
        mismatchflag=0
    M0 (net2 b0_buf net4 VSS) nmos_rf lr=60n wr=2u nr=20 sigma=1 m=1 \
        mismatchflag=0
    M44 (net0155 net0120 VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M40 (net0120 B\<3\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M37 (net0159 net0104 VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M36 (net0158 net0105 VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M35 (net0157 net0106 VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M31 (net0104 B\<2\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M30 (net0105 B\<1\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M29 (net0106 B\<0\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M18 (b3_buf b3_inv VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M16 (b3_inv B\<3\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M15 (b2_inv B\<2\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M13 (b2_buf b2_inv VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M11 (b1_buf b1_inv VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M9 (b1_inv B\<1\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    M7 (b0_buf b0_inv VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    M4 (b0_inv B\<0\> VSS VSS) nch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    M42 (net0155 net0120 VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M38 (net0120 B\<3\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M34 (net0159 net0104 VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M33 (net0158 net0105 VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M32 (net0157 net0106 VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M28 (net0104 B\<2\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M27 (net0105 B\<1\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M26 (net0106 B\<0\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M19 (b3_inv B\<3\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M17 (b3_buf b3_inv VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M14 (b2_buf b2_inv VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M12 (b2_inv B\<2\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M10 (b1_buf b1_inv VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n \
        ad=1.75e-13 as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 \
        sa=175.00n sb=175.00n sca=0 scb=0 scc=0
    M8 (b1_inv B\<1\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    M6 (b0_buf b0_inv VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    M5 (b0_inv B\<0\> VDD VDD) pch l=60n w=1u m=1 nf=1 sd=200n ad=1.75e-13 \
        as=1.75e-13 pd=2.35u ps=2.35u nrd=0.1 nrs=0.1 sa=175.00n \
        sb=175.00n sca=0 scb=0 scc=0
    I14 (b2_inv net010 VSS) res_24K
    I15 (b2_inv net07 VSS) res_24K
    I16 (b1_inv net3 VSS) res_24K
    I17 (b1_inv net1 VSS) res_24K
    I18 (b0_inv net2 VSS) res_24K
    I19 (b0_inv net4 VSS) res_24K
ends capbank_gp_lowC_noLSB_BPF
// End of subcircuit definition.

// Library name: PhasedArray_WB_V2
// Cell name: BPF4
// View name: schematic
M2 (OUTP INM VSS VSS) nmos_rf lr=120.0n wr=2.5u nr=32 sigma=1 m=1 \
        mismatchflag=0
M8 (OUTM INP VSS VSS) nmos_rf lr=120.0n wr=2.5u nr=32 sigma=1 m=1 \
        mismatchflag=0
I5 (DIG_BPF\<3\> DIG_BPF\<2\> DIG_BPF\<1\> DIG_BPF\<0\> OUTM OUTP VDDSW \
        VSS) capbank_gp_lowC_noLSB_BPF
L4 (OUTM OUTP VSS VDD_BPF0P5) spiral_sym_ct_mu_z w=7u nr=3 rad=24.0u lay=9 \
        spacing=3u gdis=10u m=1
