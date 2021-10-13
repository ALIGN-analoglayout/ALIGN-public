//
.param nfin=14 rres=2k lastt=60n fin_n_diff2sing=4 fin_p_diff2sing=6 \
    width_n_diff2sing=10 width_p_diff2sing=15 fin_n_vco_type_2=4 \
    fin_p_vco_type_2=6 fnnn=25 fppp=4 VDD=0.8 VBIAS=0.7 wpppn=1 wnnn=1

// Library name: CAD_modules
// Cell name: diff2sing_v1
// View name: schematic
.subckt diff2sing_v1 B VDD VSS in1 in2 o
.param _ar0=1 _ar1=1 _ar2=1 _ar3=1
    MP2 net3 B net1 VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MP5 net1 B VDD VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MP1 o in2 net2 VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MP4 net2 in2 net3 VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MP0 net8 in1 net4 VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MP3 net4 in1 net3 VDD lvtpfet m=1 l=14n nfin=_ar0 nf=_ar1
    MN1 net8 net8 net5 VSS lvtnfet m=1 l=14n nfin=_ar2 nf=_ar3
    MN3 net5 net8 VSS VSS lvtnfet m=1 l=14n nfin=_ar2 nf=_ar3
    MN0 o net8 net6 VSS lvtnfet m=1 l=14n nfin=_ar2 nf=_ar3
    MN2 net6 net8 VSS VSS lvtnfet m=1 l=14n nfin=_ar2 nf=_ar3
.ends diff2sing_v1

.subckt three_terminal_inv VDD VSS VBIAS VIN VOUT
.param _ar0=1 _ar1=1 _ar2=1 _ar3=1 _ar4=1 _ar5=0
    MN34 VOUT VIN net1 VSS lvtnfet m=1 l=14n nfin=_ar0 nf=_ar2
    MN33 net1 VIN VSS VSS lvtnfet m=1 l=14n nfin=_ar0 nf=_ar2
    MP34 VOUT VBIAS net2 VDD lvtpfet m=1 l=14n nfin=_ar3 nf=_ar4
    MP33 net2 VBIAS VDD VDD lvtpfet m=1 l=14n nfin=_ar3 nf=_ar4
.ends three_terminal_inv
// End of subcircuit definition.

// Library name: CAD_modules
// Cell name: VCO_type2_12
// View name: schematic
.subckt VCO_type2_65 VDD VSS o\<1\> o\<2\> o\<3\> o\<4\> o\<5\> o\<6\> \
        o\<7\> o\<8\> op\<1\> VBIAS
.param _ar0=1 _ar1=1 _ar2=1 _ar3=1 _ar4=1 _ar5=0
    xI1\<1\> VDD VSS VBIAS o\<1\> o\<2\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<2\> VDD VSS VBIAS o\<2\> o\<3\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<3\> VDD VSS VBIAS o\<3\> o\<4\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<4\> VDD VSS VBIAS o\<4\> o\<5\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<5\> VDD VSS VBIAS o\<5\> o\<6\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<6\> VDD VSS VBIAS o\<6\> o\<7\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<7\> VDD VSS VBIAS o\<7\> o\<8\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1\<8\> VDD VSS VBIAS o\<8\> op\<1\> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
.ends VCO_type2_65
// End of subcircuit definition.


// Main body of circuit:
.subckt vco_dtype_12_hierarchical VDD VSS vbias oo\<1\> oo\<2\> oo\<3\> oo\<4\> oo\<5\> oo\<6\> oo\<7\> \
oo\<8\> on\<1\> on\<2\> on\<3\> on\<4\> on\<5\> on\<6\> on\<7\> on\<8\> op\<1\> op\<2\> op\<3\> op\<4\> op\<5\> \
op\<6\> op\<7\> op\<8\>

xI6\<1\> VSS VDD VSS on\<1\> op\<1\> oo\<1\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<2\> VSS VDD VSS on\<2\> op\<2\> oo\<2\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<3\> VSS VDD VSS on\<3\> op\<3\> oo\<3\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<4\> VSS VDD VSS on\<4\> op\<4\> oo\<4\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<5\> VSS VDD VSS on\<5\> op\<5\> oo\<5\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<6\> VSS VDD VSS on\<6\> op\<6\> oo\<6\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<7\> VSS VDD VSS on\<7\> op\<7\> oo\<7\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing
xI6\<8\> VSS VDD VSS on\<8\> op\<8\> oo\<8\> diff2sing_v1 \
        _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
        _ar2=fin_n_diff2sing _ar3=width_n_diff2sing

xI1 VDD VSS op\<1\> op\<2\> op\<3\> op\<4\> op\<5\> op\<6\> op\<7\> \
        op\<8\> on\<1\> vbias VCO_type2_65 _ar0=fin_n_vco_type_2 \
        _ar1=wnnn _ar2=fnnn _ar3=fin_p_vco_type_2 _ar4=fppp \
        _ar5=wpppn

xI0 VDD VSS on\<1\> on\<2\> on\<3\> on\<4\> on\<5\> on\<6\> on\<7\> \
        on\<8\> op\<1\> vbias VCO_type2_65 _ar0=fin_n_vco_type_2 \
        _ar1=wnnn _ar2=fnnn _ar3=fin_p_vco_type_2 _ar4=fppp \
        _ar5=wpppn
.ends vco_dtype_12_hierarchical

