//
.param nfin=14 rres=2k lastt=60n fin_n_diff2sing=12 fin_p_diff2sing=12 \
    width_n_diff2sing=10 width_p_diff2sing=16 fin_n_vco_type_2=12 \
    fin_p_vco_type_2=12 fnnn=36 fppp=8 VDD=0.8 VBIAS=0.7 wpppn=1 wnnn=1


.subckt three_terminal_inv VDD VSS VBIAS VIN VOUT
.param _ar0=1 _ar1=1 _ar2=1 _ar3=1 _ar4=1 _ar5=1
    MN34 VOUT VIN net1 VSS lvtnfet m=1 l=14n nfin=_ar0 nf=_ar2
    MN33 net1 VIN VSS VSS lvtnfet m=1 l=14n nfin=_ar0 nf=_ar2
    MP34 VOUT VBIAS net2 VDD lvtpfet m=1 l=14n nfin=_ar3 nf=_ar4
    MP33 net2 VBIAS VDD VDD lvtpfet m=1 l=14n nfin=_ar3 nf=_ar4
.ends three_terminal_inv
// End of subcircuit definition.

// Library name: CAD_modules
// Cell name: VCO_type2_12
// View name: schematic
.subckt VCO_type2_65 VDD VSS o<1> o<2> o<3> o<4> o<5> o<6> \
        o<7> o<8> op<1> VBIAS
.param _ar0=fin_p_diff2sing _ar1=width_p_diff2sing \
_ar2=fin_n_diff2sing _ar3=width_n_diff2sing _ar4=fppp \
_ar5=wppn
    xI1<1> VDD VSS VBIAS o<1> o<2> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<2> VDD VSS VBIAS o<2> o<3> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<3> VDD VSS VBIAS o<3> o<4> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<4> VDD VSS VBIAS o<4> o<5> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<5> VDD VSS VBIAS o<5> o<6> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<6> VDD VSS VBIAS o<6> o<7> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<7> VDD VSS VBIAS o<7> o<8> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
    xI1<8> VDD VSS VBIAS o<8> op<1> three_terminal_inv _ar0=_ar0 \
        _ar1=_ar1 _ar2=_ar2 _ar3=_ar3 _ar4=_ar4 _ar5=_ar5
.ends VCO_type2_65

