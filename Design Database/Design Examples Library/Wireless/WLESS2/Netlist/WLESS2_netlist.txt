
// Library name: test_qmeng
// Cell name: MIXER_RFBIAS_RES
// View name: schematic
subckt MIXER_RFBIAS_RES M P tail_bias
R3 (P net9 ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R0 (net9 tail_bias ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R1 (tail_bias net05 ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R2 (net05 M ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

ends MIXER_RFBIAS_RES
// End of subcircuit definition.

// Library name: test_qmeng
// Cell name: MIXER_LOSWBIAS_RES
// View name: schematic
subckt MIXER_LOSWBIAS_RES MIXER_LOBIAS VDD VSS
R5 (VDD net050 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R4 (net031 net034 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R9 (net049 net031 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R6 (net050 net051 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R7 (net051 MIXER_LOBIAS ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R8 (MIXER_LOBIAS net049 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R0 (net039 VSS ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R1 (net033 net039 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R3 (net034 net036 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

R2 (net036 net033 ) rppolywo l=4u w=1u m=1 mf=(1) mismatchflag=0

ends MIXER_LOSWBIAS_RES
// End of subcircuit definition.

// Library name: test_qmeng
// Cell name: MIXER_LOAD_RES
// View name: schematic
subckt MIXER_LOAD_RES A B
R4 (net03 B ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R0 (A net06 ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R1 (net06 net05 ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R3 (net05 net03 ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

ends MIXER_LOAD_RES
// End of subcircuit definition.

// Library name: PhasedArray_WB_V2
// Cell name: Mixer
// View name: schematic
M35 (net051 tailm VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=12 sigma=1 m=1 \
        mismatchflag=0
M34 (net039 tailp VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=12 sigma=1 m=1 \
        mismatchflag=0
M44\<1\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<2\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<3\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<4\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<5\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<6\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<7\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M44\<8\> (VSS MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M43 (VSS VSS VSS VSS) nmos_rf lr=60n wr=2u nr=4 sigma=1 m=2 mismatchflag=0
M38 (MIXER_TAIL_IIN MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 \
        sigma=1 m=1 mismatchflag=0
M39 (pbias MIXER_TAIL_IIN VSS VSS) nmos_rf lr=240.0n wr=3.6u nr=2 sigma=1 \
        m=1 mismatchflag=0
M7 (IFM Oscp net039 net039) nmos_rf lr=60n wr=2u nr=4 sigma=1 m=1 \
        mismatchflag=0
M13 (IFP Oscp net051 net051) nmos_rf lr=60n wr=2u nr=4 sigma=1 m=1 \
        mismatchflag=0
M12 (IFM Oscm net051 net051) nmos_rf lr=60n wr=2u nr=4 sigma=1 m=1 \
        mismatchflag=0
M11 (IFP Oscm net039 net039) nmos_rf lr=60n wr=2u nr=4 sigma=1 m=1 \
        mismatchflag=0
M29 (VDD VDD VDD VDD) pmos_rf lr=240.0n wr=2.05u nr=8 sigma=1 m=2 \
        mismatchflag=0
M16 (pbias pbias VDD VDD) pmos_rf lr=240.0n wr=2.05u nr=8 sigma=1 m=2 \
        mismatchflag=0
M24 (IFP pbias VDD VDD) pmos_rf lr=240.0n wr=2.05u nr=32 sigma=1 m=2 \
        mismatchflag=0
M23 (IFM pbias VDD VDD) pmos_rf lr=240.0n wr=2.05u nr=32 sigma=1 m=2 \
        mismatchflag=0
I29 (tailm tailp MIXER_TAIL_IIN) MIXER_RFBIAS_RES
I12 (Oscp VDD VSS) MIXER_LOSWBIAS_RES
I21 (Oscm VDD VSS) MIXER_LOSWBIAS_RES
I18 (IFP VDD) MIXER_LOAD_RES
I17 (IFM VDD) MIXER_LOAD_RES
R1\<1\> (VSS net040\<0\> ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R1\<2\> (VSS net040\<1\> ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R1\<3\> (VSS net040\<2\> ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

R1\<4\> (VSS net040\<3\> ) rppolys l=13.0u w=1u m=1 mf=(1) mismatchflag=0

C15 (LOP Oscp VSS) mimcap_woum_sin_rf lt=32.0u wt=16.0u lay=7 m=1 \
        mimflag=3 mismatchflag=0
C6 (RFM tailm VSS) mimcap_woum_sin_rf lt=22.0u wt=22.0u lay=7 m=1 \
        mimflag=3 mismatchflag=0
C7 (RFP tailp VSS) mimcap_woum_sin_rf lt=22.0u wt=22.0u lay=7 m=1 \
        mimflag=3 mismatchflag=0
C14 (LOM Oscm VSS) mimcap_woum_sin_rf lt=32.0u wt=16.0u lay=7 m=1 \
        mimflag=3 mismatchflag=0
R2 (IFP OUTP ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R5\<1\> (VSS net043\<0\> ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R5\<2\> (VSS net043\<1\> ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R5\<3\> (VSS net043\<2\> ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R5\<4\> (VSS net043\<3\> ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

R0 (OUTM IFM ) rppolywo l=6u w=1u m=1 mf=(1) mismatchflag=0

