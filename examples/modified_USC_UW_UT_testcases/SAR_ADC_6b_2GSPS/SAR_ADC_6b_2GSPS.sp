// Generated for: spectre
// Generated on: May  8 13:52:56 2019
// Design library name: POSH_SPICE_6b2GSPS
// Design cell name: TB_ADC
// Design view name: schematic
 * simulatorlang=spectre
* global 0
parameters pt=511 SW_RS2=4 SW_Lch2=8 SW_RS=4 SW_Pch=8 SW_LOAD=16 CL_SH=5f \
    Cu=2f Fs=2G PWR=0.8 RNN=4 RNP=4 SNN=56 SNP=56 Fin=Fs*pt/1024
* include "/home/techfile/PTM/ASAP/ASAP7_PDKandLIB_v1p5/asap7PDK_r1p5/models/hspice/7nm_TT_160803.pm"

// Library name: POSH_SPICE_6b2GSPS
// Cell name: BUF_X4
// View name: schematic
.subckt BUF_X4 Y VDD VNW VPW VSS A
    I2 Y net027 VSS VPW slvtnfet w=81n l=14n m=4
    I0 net027 A VSS VPW slvtnfet w=81n l=14n m=2
    I3 Y net027 VDD VNW slvtpfet w=81n l=14n m=4
    I1 net027 A VDD VNW slvtpfet w=81n l=14n m=2
.ends BUF_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: INV_X4
// View name: schematic
.subckt INV_X4 Y VDD VNW VPW VSS A
    I2 Y A VSS VPW slvtnfet w=81n l=14n m=4
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=4
.ends INV_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: INV_X6
// View name: schematic
.subckt INV_X6 Y VDD VNW VPW VSS A
    I2 Y A VSS VPW slvtnfet w=81n l=14n m=6
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=6
.ends INV_X6
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: BUF_X12
// View name: schematic
.subckt BUF_X12 Y VDD VNW VPW VSS A
    I2 Y net027 VSS VPW slvtnfet w=81n l=14n m=12
    I0 net027 A VSS VPW slvtnfet w=81n l=14n m=3
    I3 Y net027 VDD VNW slvtpfet w=81n l=14n m=12
    I1 net027 A VDD VNW slvtpfet w=81n l=14n m=3
.ends BUF_X12
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: DLY2_X2
// View name: schematic
.subckt DLY2_X2 Y VDD VNW VPW VSS A
    MMPA0 ny A i1 VNW slvtpfet w=81n l=14n m=1
    MMPA1 i1 A VDD VNW slvtpfet w=81n l=14n m=1
    MMPY Y ny VDD VNW slvtpfet w=81n l=14n m=1
    MMPY_2 Y ny VDD VNW slvtpfet w=81n l=14n m=1
    MMNA0 ny A i0 VPW slvtnfet w=81n l=14n m=1
    MMNA1 i0 A VSS VPW slvtnfet w=81n l=14n m=1
    MMNY Y ny VSS VPW slvtnfet w=81n l=14n m=1
    MMNY_2 Y ny VSS VPW slvtnfet w=81n l=14n m=1
.ends DLY2_X2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: INV_X16
// View name: schematic
.subckt INV_X16 Y VDD VNW VPW VSS A
    I2 Y A VSS VPW slvtnfet w=81n l=14n m=16
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=16
.ends INV_X16
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: INV_X8
// View name: schematic
.subckt INV_X8 Y VDD VNW VPW VSS A
    I2 Y A VSS VPW slvtnfet w=81n l=14n m=8
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=8
.ends INV_X8
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: BUF_X6
// View name: schematic
.subckt BUF_X6 Y VDD VNW VPW VSS A
    I2 Y net027 VSS VPW slvtnfet w=81n l=14n m=6
    I0 net027 A VSS VPW slvtnfet w=81n l=14n m=2
    I3 Y net027 VDD VNW slvtpfet w=81n l=14n m=6
    I1 net027 A VDD VNW slvtpfet w=81n l=14n m=2
.ends BUF_X6
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: NAND2_X4
// View name: schematic
.subckt NAND2_X4 Y VDD VNW VPW VSS A B
    I1 Y A net13 VPW slvtnfet w=81n l=14n m=6
    I2 net13 B VSS VPW slvtnfet w=81n l=14n m=6
    I0 Y B VDD VNW slvtpfet w=81n l=14n m=4
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=4
.ends NAND2_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: DLY4_X4
// View name: schematic
.subckt DLY4_X4 Y VDD VNW VPW VSS A
    MMPA0 na A p0 VNW slvtpfet w=81n l=14n m=1
    MMPA1 p0 A VDD VNW slvtpfet w=81n l=14n m=1
    MMPna1 p1 na VDD VNW slvtpfet w=81n l=14n m=1
    MMPna0 ba na p1 VNW slvtpfet w=81n l=14n m=1
    MMPba1 p2 ba VDD VNW slvtpfet w=81n l=14n m=1
    MMPba0 nba ba p2 VNW slvtpfet w=81n l=14n m=1
    MMPY Y nba VDD VNW slvtpfet w=81n l=14n m=1
    MMPY_4 Y nba VDD VNW slvtpfet w=81n l=14n m=1
    MMPY_3 Y nba VDD VNW slvtpfet w=81n l=14n m=1
    MMPY_2 Y nba VDD VNW slvtpfet w=81n l=14n m=1
    MMNA0 na A n0 VPW slvtnfet w=81n l=14n m=1
    MMNA1 n0 A VSS VPW slvtnfet w=81n l=14n m=1
    MMNba0 nba ba n2 VPW slvtnfet w=81n l=14n m=1
    MMNba1 n2 ba VSS VPW slvtnfet w=81n l=14n m=1
    MMNna1 n1 na VSS VPW slvtnfet w=81n l=14n m=1
    MMNna0 ba na n1 VPW slvtnfet w=81n l=14n m=1
    MMNY_2 Y nba VSS VPW slvtnfet w=81n l=14n m=1
    MMNY_3 Y nba VSS VPW slvtnfet w=81n l=14n m=1
    MMNY_4 Y nba VSS VPW slvtnfet w=81n l=14n m=1
    MMNY Y nba VSS VPW slvtnfet w=81n l=14n m=1
.ends DLY4_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB3_CLK1
// View name: schematic
.subckt SUB3_CLK1 CK_E I QIP QSN QSP QS_DEL_more VDD VSS
    I25 net073 VDD VDD VSS VSS QS_DEL BUF_X4
    I43 net025 VDD VDD VSS VSS QS_DEL_more INV_X4
    I27 QS_DEL_more VDD VDD VSS VSS net062 INV_X4
    I108 QS_DEL VDD VDD VSS VSS net062 INV_X6
    I100 net37 VDD VDD VSS VSS net35 INV_X6
    I121 CK_E VDD VDD VSS VSS net074 BUF_X12
    I97 net033 VDD VDD VSS VSS I BUF_X12
    C13 QS_DEL VSS capacitor c=4f
    C10 net060 VSS capacitor c=4f
    C11 net061 VSS capacitor c=4f
    C12 net062 VSS capacitor c=4f
    C5 net35 VSS capacitor c=6f
    C15 net37 VSS capacitor c=6f
    C7 net011 VSS capacitor c=6f
    I41 net026 VDD VDD VSS VSS net019 DLY2_X2
    I104 net061 VDD VDD VSS VSS net060 DLY2_X2
    I102 net062 VDD VDD VSS VSS net061 DLY2_X2
    I18 net35 VDD VDD VSS VSS net011 DLY2_X2
    I46 net011 VDD VDD VSS VSS net033 DLY2_X2
    I109 QSP VDD VDD VSS VSS net076 INV_X16
    I111 QSN VDD VDD VSS VSS net057 INV_X16
    I120 QIP VDD VDD VSS VSS net025 INV_X8
    I110 net076 VDD VDD VSS VSS net057 INV_X8
    I112 net057 VDD VDD VSS VSS net073 BUF_X6
    I40 net074 VDD VDD VSS VSS net019 net026 NAND2_X4
    I101 net069 VDD VDD VSS VSS net37 net033 NAND2_X4
    I29 net019 VDD VDD VSS VSS net060 DLY4_X4
    I22 net060 VDD VDD VSS VSS net069 DLY4_X4
.ends SUB3_CLK1
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: INV_X2
// View name: schematic
.subckt INV_X2 Y VDD VNW VPW VSS A
    I2 Y A VSS VPW slvtnfet w=81n l=14n m=2
    I3 Y A VDD VNW slvtpfet w=81n l=14n m=2
.ends INV_X2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB2_RDYgen
// View name: schematic
.subckt SUB2_RDYgen IN IP RDY RS VDD VSS
    M1 net45 IN VSS VSS slvtnfet w=81n l=14n m=4
    M2 net45 IP VSS VSS slvtnfet w=81n l=14n m=4
    I102 net46 VDD VDD VSS VSS RS INV_X2
    I100 RDY VDD VDD VSS VSS net45 INV_X8
    M0 net45 net46 VDD VDD slvtpfet w=81n l=14n m=8
.ends SUB2_RDYgen
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB2_COMP_DynamicLAT
// View name: schematic
.subckt SUB2_COMP_DynamicLAT DN DP IN IP VDD VSS
    I95 DN VDD VDD VSS VSS net113 INV_X8
    I94 DP VDD VDD VSS VSS net17 INV_X8
    M2 net17 IP VDD VDD slvtpfet w=81n l=14n m=SW_RS2
    M3 net113 IN VDD VDD slvtpfet w=81n l=14n m=SW_RS2
    M5 net113 net17 VDD VDD slvtpfet w=81n l=14n m=SW_Lch2
    M4 net17 net113 VDD VDD slvtpfet w=81n l=14n m=SW_Lch2
    M6 net17 IP net112 VSS slvtnfet w=81n l=14n m=SW_Lch2
    M7 net113 IN net111 VSS slvtnfet w=81n l=14n m=SW_Lch2
    M0 net112 net113 VSS VSS slvtnfet w=81n l=14n m=SW_Lch2
    M1 net111 net17 VSS VSS slvtnfet w=81n l=14n m=SW_Lch2
.ends SUB2_COMP_DynamicLAT
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB2_COMP_DynamicAMP
// View name: schematic
.subckt SUB2_COMP_DynamicAMP AN AP CK ON OP RS VDD VSS
    I65 ON RS VSS VSS slvtnfet w=81n l=14n m=SW_RS
    M8 OP RS VSS VSS slvtnfet w=81n l=14n m=SW_RS
    I62 OP AP OP VDD slvtpfet w=81n l=14n m=SW_Pch
    I61 ON AN ON VDD slvtpfet w=81n l=14n m=SW_Pch
    M0 net016 CK VDD VDD slvtpfet w=81n l=14n m=SW_Pch
    I59 ON AP net016 VDD slvtpfet w=81n l=14n m=SW_Pch
    I63 VDD ON VDD VDD slvtpfet w=81n l=14n m=SW_LOAD
    I64 VDD OP VDD VDD slvtpfet w=81n l=14n m=SW_LOAD
    I60 OP AN net016 VDD slvtpfet w=81n l=14n m=SW_Pch
.ends SUB2_COMP_DynamicAMP
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB2_COMP_DUPLEX
// View name: schematic
.subckt SUB2_COMP_DUPLEX DN\<1\> DN\<2\> DP\<1\> DP\<2\> INN INP LAT\<1\> \
        LAT\<2\> RDY\<1\> RDY\<2\> RS\<1\> RS\<2\> VDD VSS
    I127 CompN2 CompP2 RDY\<2\> RS\<2\> VDD VSS SUB2_RDYgen
    I126 CompN1 CompP1 RDY\<1\> RS\<1\> VDD VSS SUB2_RDYgen
    I124 DN\<1\> DP\<1\> CompN1 CompP1 VDD VSS SUB2_COMP_DynamicLAT
    I125 DN\<2\> DP\<2\> CompN2 CompP2 VDD VSS SUB2_COMP_DynamicLAT
    I18 INN INP LAT\<1\> CompN1 CompP1 RS\<1\> VDD VSS \
        SUB2_COMP_DynamicAMP
    I24 INN INP LAT\<2\> CompN2 CompP2 RS\<2\> VDD VSS \
        SUB2_COMP_DynamicAMP
.ends SUB2_COMP_DUPLEX
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB1_CDAC_SW
// View name: schematic
.subckt SUB1_CDAC_SW CTRL_nch N O REFN REFP VDD VSS
    M0 N CTRL_nch REFP VDD slvtpfet w=81n l=14n m=RNN
    C0 O N capacitor c=Cu ic=0
    M1 N CTRL_nch REFN VSS slvtnfet w=81n l=14n m=RNP
.ends SUB1_CDAC_SW
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB1_CDAC_6b
// View name: schematic
.subckt SUB1_CDAC_6b CTRL_nch\<5\> CTRL_nch\<4\> CTRL_nch\<3\> \
        CTRL_nch\<2\> CTRL_nch\<1\> CTRL_nch\<0\> I O QSN QSP REFN REFP \
        VDD VSS
    M0 O QSP I VSS slvtnfet w=186n l=14n m=SNN
    I2 CTRL_nch\<1\> net33 O REFN REFP VDD VSS SUB1_CDAC_SW
    I4\<4\> CTRL_nch\<3\> net056\<0\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I4\<3\> CTRL_nch\<3\> net056\<1\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I4\<2\> CTRL_nch\<3\> net056\<2\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I4\<1\> CTRL_nch\<3\> net056\<3\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I3\<2\> CTRL_nch\<2\> net076\<0\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I3\<1\> CTRL_nch\<2\> net076\<1\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I1 CTRL_nch\<0\> net32 O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<8\> CTRL_nch\<4\> net055\<0\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<7\> CTRL_nch\<4\> net055\<1\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<6\> CTRL_nch\<4\> net055\<2\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<5\> CTRL_nch\<4\> net055\<3\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<4\> CTRL_nch\<4\> net055\<4\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<3\> CTRL_nch\<4\> net055\<5\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<2\> CTRL_nch\<4\> net055\<6\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I5\<1\> CTRL_nch\<4\> net055\<7\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<16\> CTRL_nch\<5\> net054\<0\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<15\> CTRL_nch\<5\> net054\<1\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<14\> CTRL_nch\<5\> net054\<2\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<13\> CTRL_nch\<5\> net054\<3\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<12\> CTRL_nch\<5\> net054\<4\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<11\> CTRL_nch\<5\> net054\<5\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<10\> CTRL_nch\<5\> net054\<6\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<9\> CTRL_nch\<5\> net054\<7\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<8\> CTRL_nch\<5\> net054\<8\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<7\> CTRL_nch\<5\> net054\<9\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<6\> CTRL_nch\<5\> net054\<10\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<5\> CTRL_nch\<5\> net054\<11\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<4\> CTRL_nch\<5\> net054\<12\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<3\> CTRL_nch\<5\> net054\<13\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<2\> CTRL_nch\<5\> net054\<14\> O REFN REFP VDD VSS SUB1_CDAC_SW
    I6\<1\> CTRL_nch\<5\> net054\<15\> O REFN REFP VDD VSS SUB1_CDAC_SW
    M1 I QSN O VDD slvtpfet w=186n l=14n m=SNP
.ends SUB1_CDAC_6b
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB1_CDAC_6b_diff
// View name: schematic
.subckt SUB1_CDAC_6b_diff CTRLn\<5\> CTRLn\<4\> CTRLn\<3\> CTRLn\<2\> \
        CTRLn\<1\> CTRLp\<5\> CTRLp\<4\> CTRLp\<3\> CTRLp\<2\> CTRLp\<1\> \
        IN IP ON OP QSN QSP REFN REFP VDD VSS
    C17 OP VSS capacitor c=CL_SH
    C10 ON VSS capacitor c=CL_SH
    I21 CTRLp\<5\> CTRLp\<4\> CTRLp\<3\> CTRLp\<2\> CTRLp\<1\> VSS IP OP \
        QSN QSP REFN REFP VDD VSS SUB1_CDAC_6b
    I12 CTRLn\<5\> CTRLn\<4\> CTRLn\<3\> CTRLn\<2\> CTRLn\<1\> VSS IN ON \
        QSN QSP REFN REFP VDD VSS SUB1_CDAC_6b
.ends SUB1_CDAC_6b_diff
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: DFFQ_X2
// View name: schematic
.subckt DFFQ_X2 Q VDD VNW VPW VSS CK D
    MMPI0 nm bclk i1 VNW slvtpfet w=81n l=14n m=1
    MMPI1 i1 D VDD VNW slvtpfet w=81n l=14n m=1
    MMPMF1 mf1 m VDD VNW slvtpfet w=81n l=14n m=1
    MMPMF0 nm nclk mf1 VNW slvtpfet w=81n l=14n m=1
    MMPSLF0 s bclk slf1 VNW slvtpfet w=81n l=14n m=1
    MMPSLF1 slf1 ns VDD VNW slvtpfet w=81n l=14n m=1
    MMPCKIN0 nclk CK VDD VNW slvtpfet w=81n l=14n m=1
    MMPMI0 m nm VDD VNW slvtpfet w=81n l=14n m=1
    MMPCKOUT0 bclk nclk VDD VNW slvtpfet w=81n l=14n m=1
    MMPSLT0 s nclk m VNW slvtpfet w=81n l=14n m=1
    MMPSLI0 ns s VDD VNW slvtpfet w=81n l=14n m=1
    MMPQ Q ns VDD VNW slvtpfet w=81n l=14n m=1
    MMPQ_2 Q ns VDD VNW slvtpfet w=81n l=14n m=1
    MMNI1 i0 D VSS VPW slvtnfet w=81n l=14n m=1
    MMNI0 nm nclk i0 VPW slvtnfet w=81n l=14n m=1
    MMNCKIN0 nclk CK VSS VPW slvtnfet w=81n l=14n m=1
    MMNMF0 nm bclk mf0 VPW slvtnfet w=81n l=14n m=1
    MMNMF1 mf0 m VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLF0 s nclk slf0 VPW slvtnfet w=81n l=14n m=1
    MMNSLF1 slf0 ns VSS VPW slvtnfet w=81n l=14n m=1
    MMNMI0 m nm VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLT0 s bclk m VPW slvtnfet w=81n l=14n m=1
    MMNCKOU0 bclk nclk VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLI0 ns s VSS VPW slvtnfet w=81n l=14n m=1
    MMNQ Q ns VSS VPW slvtnfet w=81n l=14n m=1
    MMNQ_2 Q ns VSS VPW slvtnfet w=81n l=14n m=1
.ends DFFQ_X2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: DFFRPQN_X3
// View name: schematic
.subckt DFFRPQN_X3 QN VDD VNW VPW VSS CK D R
    MMNI1 i0 D VSS VPW slvtnfet w=81n l=14n m=1
    MMNI0 nm nclk i0 VPW slvtnfet w=81n l=14n m=1
    MMNMF0 nm bclk mf0 VPW slvtnfet w=81n l=14n m=1
    MMNMF1 mf0 m VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLF1 slf0 ns VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLF0 s nclk slf0 VPW slvtnfet w=81n l=14n m=1
    MMNCKIN0 nclk CK VSS VPW slvtnfet w=81n l=14n m=1
    MMNCKOUT0 bclk nclk VSS VPW slvtnfet w=81n l=14n m=1
    MMNMR0 m nm VSS VPW slvtnfet w=81n l=14n m=1
    MMNMR1 m R VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLT0 s bclk m VPW slvtnfet w=81n l=14n m=1
    MMNSLF2 s R VSS VPW slvtnfet w=81n l=14n m=1
    MMNSLI0 ns s VSS VPW slvtnfet w=81n l=14n m=1
    MMNQN_2 QN s VSS VPW slvtnfet w=81n l=14n m=1
    MMNQN_3 QN s VSS VPW slvtnfet w=81n l=14n m=1
    MMNQN QN s VSS VPW slvtnfet w=81n l=14n m=1
    MMPI0 nm bclk i1 VNW slvtpfet w=81n l=14n m=1
    MMPI1 i1 D VDD VNW slvtpfet w=81n l=14n m=1
    MMPSLF1 slf1 ns slf2 VNW slvtpfet w=81n l=14n m=1
    MMPSLF2 slf2 R VDD VNW slvtpfet w=81n l=14n m=1
    MMPSLF0 s bclk slf1 VNW slvtpfet w=81n l=14n m=1
    MMPMF0 nm nclk mf1 VNW slvtpfet w=81n l=14n m=1
    MMPMF1 mf1 m VDD VNW slvtpfet w=81n l=14n m=1
    MMPMR0 m nm mr0 VNW slvtpfet w=81n l=14n m=1
    MMPMR1 mr0 R VDD VNW slvtpfet w=81n l=14n m=1
    MMPCKIN0 nclk CK VDD VNW slvtpfet w=81n l=14n m=1
    MMPCKOUT0 bclk nclk VDD VNW slvtpfet w=81n l=14n m=1
    MMPSLT0 s nclk m VNW slvtpfet w=81n l=14n m=1
    MMPSLI0 ns s VDD VNW slvtpfet w=81n l=14n m=1
    MMPQN QN s VDD VNW slvtpfet w=81n l=14n m=1
    MMPQN_3 QN s VDD VNW slvtpfet w=81n l=14n m=1
    MMPQN_2 QN s VDD VNW slvtpfet w=81n l=14n m=1
.ends DFFRPQN_X3
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB4_SAR2_DFF
// View name: schematic
.subckt SUB4_SAR2_DFF CKP D DN DP NN PN RSP VDD VSS
    I81 D VDD VDD VSS VSS NN INV_X2
    I83 NN VDD VDD VSS VSS CKP DN RSP DFFRPQN_X3
    I80 PN VDD VDD VSS VSS CKP DP RSP DFFRPQN_X3
.ends SUB4_SAR2_DFF
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: BUF_X2
// View name: schematic
.subckt BUF_X2 Y VDD VNW VPW VSS A
    I2 Y net08 VSS VPW slvtnfet w=81n l=14n m=2
    I0 net08 A VSS VPW slvtnfet w=81n l=14n m=1
    I3 Y net08 VDD VNW slvtpfet w=81n l=14n m=2
    I1 net08 A VDD VNW slvtpfet w=81n l=14n m=1
.ends BUF_X2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB4_SAR3
// View name: schematic
.subckt SUB4_SAR3 CKP D DN DP VDD VSS
    I46 DP CKP net010 VSS slvtnfet w=81n l=14n m=8
    N14 D CKP DN VSS slvtnfet w=81n l=14n m=8
    I42 D VDD VDD VSS VSS net010 INV_X2
    I43 net010 VDD VDD VSS VSS D INV_X2
.ends SUB4_SAR3
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB4_SAR1_DFF
// View name: schematic
.subckt SUB4_SAR1_DFF CKP D DN DP NN PN RSP VDD VSS
    I82 PN VDD VDD VSS VSS net027 INV_X2
    I81 NN VDD VDD VSS VSS D INV_X2
    I83 net027 VDD VDD VSS VSS CKP DN RSP DFFRPQN_X3
    I80 D VDD VDD VSS VSS CKP DP RSP DFFRPQN_X3
.ends SUB4_SAR1_DFF
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB4_SAR_TOP
// View name: schematic
.subckt SUB4_SAR_TOP CKP\<5\> CKP\<4\> CKP\<3\> CKP\<2\> CKP\<1\> CKP\<0\> \
        D\<5\> D\<4\> D\<3\> D\<2\> D\<1\> D\<0\> DN1 DN2 DP1 DP2 INITP \
        N_Nch\<5\> N_Nch\<4\> N_Nch\<3\> N_Nch\<2\> N_Nch\<1\> P_Nch\<5\> \
        P_Nch\<4\> P_Nch\<3\> P_Nch\<2\> P_Nch\<1\> QM VDD VSS
    I46\<5\> DM\<5\> VDD VDD VSS VSS net088 net090\<0\> DFFQ_X2
    I46\<4\> DM\<4\> VDD VDD VSS VSS net088 net090\<1\> DFFQ_X2
    I46\<3\> DM\<3\> VDD VDD VSS VSS net088 net090\<2\> DFFQ_X2
    I46\<2\> DM\<2\> VDD VDD VSS VSS net088 net090\<3\> DFFQ_X2
    I46\<1\> DM\<1\> VDD VDD VSS VSS net088 net090\<4\> DFFQ_X2
    I43\<5\> D\<5\> VDD VDD VSS VSS net078 DM\<5\> DFFQ_X2
    I43\<4\> D\<4\> VDD VDD VSS VSS net078 DM\<4\> DFFQ_X2
    I43\<3\> D\<3\> VDD VDD VSS VSS net078 DM\<3\> DFFQ_X2
    I43\<2\> D\<2\> VDD VDD VSS VSS net078 DM\<2\> DFFQ_X2
    I43\<1\> D\<1\> VDD VDD VSS VSS net078 DM\<1\> DFFQ_X2
    I43\<0\> D\<0\> VDD VDD VSS VSS net078 DM\<0\> DFFQ_X2
    I5 CKP\<1\> DL\<1\> DP1 DN1 net073 net074 INITP VDD VSS \
        SUB4_SAR2_DFF
    I40 CKP\<4\> DL\<4\> DP2 DN2 net079 net080 INITP VDD VSS \
        SUB4_SAR2_DFF
    I10 CKP\<3\> DL\<3\> DP1 DN1 net077 net0102 INITP VDD VSS \
        SUB4_SAR2_DFF
    I4 CKP\<2\> DL\<2\> DP2 DN2 net075 net076 INITP VDD VSS \
        SUB4_SAR2_DFF
    I51\<5\> net090\<0\> VDD VDD VSS VSS net093\<0\> BUF_X2
    I51\<4\> net090\<1\> VDD VDD VSS VSS net093\<1\> BUF_X2
    I51\<3\> net090\<2\> VDD VDD VSS VSS net093\<2\> BUF_X2
    I51\<2\> net090\<3\> VDD VDD VSS VSS net093\<3\> BUF_X2
    I51\<1\> net090\<4\> VDD VDD VSS VSS net093\<4\> BUF_X2
    I49\<5\> net093\<0\> VDD VDD VSS VSS DL\<5\> BUF_X2
    I49\<4\> net093\<1\> VDD VDD VSS VSS DL\<4\> BUF_X2
    I49\<3\> net093\<2\> VDD VDD VSS VSS DL\<3\> BUF_X2
    I49\<2\> net093\<3\> VDD VDD VSS VSS DL\<2\> BUF_X2
    I49\<1\> net093\<4\> VDD VDD VSS VSS DL\<1\> BUF_X2
    I28 N_Nch\<4\> VDD VDD VSS VSS net086 INV_X8
    I25 N_Nch\<5\> VDD VDD VSS VSS net0100 INV_X8
    I18 P_Nch\<4\> VDD VDD VSS VSS net091 INV_X8
    I15 P_Nch\<5\> VDD VDD VSS VSS net092 INV_X8
    I32 net083 VDD VDD VSS VSS net073 INV_X4
    I31 net084 VDD VDD VSS VSS net075 INV_X4
    I29 net085 VDD VDD VSS VSS net077 INV_X4
    I27 net086 VDD VDD VSS VSS net079 INV_X4
    I26 net0100 VDD VDD VSS VSS net081 INV_X4
    I23 net099 VDD VDD VSS VSS net074 INV_X4
    I22 net089 VDD VDD VSS VSS net076 INV_X4
    I19 net0101 VDD VDD VSS VSS net0102 INV_X4
    I17 net091 VDD VDD VSS VSS net080 INV_X4
    I16 net092 VDD VDD VSS VSS net082 INV_X4
    I48 net087 VDD VDD VSS VSS QM INV_X4
    I47 net088 VDD VDD VSS VSS net087 INV_X4
    I45 net078 VDD VDD VSS VSS QM INV_X4
    I44 CKP\<0\> DM\<0\> DP2 DN2 VDD VSS SUB4_SAR3
    I33 N_Nch\<1\> VDD VDD VSS VSS net083 INV_X6
    I30 N_Nch\<2\> VDD VDD VSS VSS net084 INV_X6
    I34 N_Nch\<3\> VDD VDD VSS VSS net085 INV_X6
    I24 P_Nch\<1\> VDD VDD VSS VSS net099 INV_X6
    I21 P_Nch\<2\> VDD VDD VSS VSS net089 INV_X6
    I20 P_Nch\<3\> VDD VDD VSS VSS net0101 INV_X6
    I8 CKP\<5\> DL\<5\> DP1 DN1 net081 net082 INITP VDD VSS \
        SUB4_SAR1_DFF
.ends SUB4_SAR_TOP
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: NAND2_X3
// View name: schematic
.subckt NAND2_X3 Y VDD VNW VPW VSS A B
    MMPB Y B VDD VNW slvtpfet w=81n l=14n m=1
    MMPB_3 Y B VDD VNW slvtpfet w=81n l=14n m=1
    MMPB_2 Y B VDD VNW slvtpfet w=81n l=14n m=1
    MMPA Y A VDD VNW slvtpfet w=81n l=14n m=1
    MMPA_3 Y A VDD VNW slvtpfet w=81n l=14n m=1
    MMPA_2 Y A VDD VNW slvtpfet w=81n l=14n m=1
    MMNA Y A n0 VPW slvtnfet w=81n l=14n m=1
    MMNA_3 Y A n0 VPW slvtnfet w=81n l=14n m=1
    MMNA_2 Y A n0 VPW slvtnfet w=81n l=14n m=1
    MMNB n0 B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_3 n0 B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_2 n0 B VSS VPW slvtnfet w=81n l=14n m=1
.ends NAND2_X3
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: NOR2_X4
// View name: schematic
.subckt NOR2_X4 Y VDD VNW VPW VSS A B
    MMPB p0 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPB_4 p0 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPB_3 p0 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPB_2 p0 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPA Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMPA_4 Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMPA_3 Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMPA_2 Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMNB Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_4 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_3 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_2 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNA Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_4 Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_3 Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_2 Y A VSS VPW slvtnfet w=81n l=14n m=1
.ends NOR2_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: TIEHI_X1
// View name: schematic
.subckt TIEHI_X1 Y VDD VNW VPW VSS
    M1 lo hi VSS VPW slvtnfet w=81n l=14n m=1
    M0 VSS lo VSS VPW slvtnfet w=81n l=14n m=1
    M4 lo lo VSS VPW slvtnfet w=81n l=14n m=1
    M3 hi hi VDD VNW slvtpfet w=81n l=14n m=2
    M5 Y lo VDD VNW slvtpfet w=81n l=14n m=2
    M2 hi lo VDD VNW slvtpfet w=81n l=14n m=2
.ends TIEHI_X1
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB5_SEQ_6b
// View name: schematic
.subckt SUB5_SEQ_6b CKP\<5\> CKP\<4\> CKP\<3\> CKP\<2\> CKP\<1\> CKP\<0\> \
        ENV\<2\> ENV\<3\> FLAG QSP RDY1 RDY2 VDD VSS
    I27 net038 VDD VDD VSS VSS RDY1 BUF_X4
    I26 net034 VDD VDD VSS VSS RDY2 BUF_X4
    I191 net079 VDD VDD VSS VSS net052 net050 NAND2_X3
    I63 net060 VDD VDD VSS VSS QSP net065 NAND2_X3
    I142 CKP\<0\> VDD VDD VSS VSS net069 INV_X4
    I138 CKP\<1\> VDD VDD VSS VSS net052 INV_X4
    I132 CKP\<2\> VDD VDD VSS VSS net046 INV_X4
    I130 CKP\<3\> VDD VDD VSS VSS net087 INV_X4
    I123 CKP\<5\> VDD VDD VSS VSS net085 INV_X4
    I73 RSn\<7\> VDD VDD VSS VSS net063 INV_X4
    I67 ENV\<2\> VDD VDD VSS VSS net086 INV_X4
    I68 ENV\<3\> VDD VDD VSS VSS net087 INV_X4
    I126 CKP\<4\> VDD VDD VSS VSS net086 INV_X4
    I8 FLAG VDD VDD VSS VSS net068 net079 NOR2_X4
    I117 RSn\<4\> VDD VDD VSS VSS net046 INV_X2
    I119 RSn\<3\> VDD VDD VSS VSS net052 INV_X2
    I113 RSn\<6\> VDD VDD VSS VSS net086 INV_X2
    I193 net050 VDD VDD VSS VSS net34 INV_X2
    I9 net068 VDD VDD VSS VSS net083 INV_X2
    I114 RSn\<5\> VDD VDD VSS VSS net087 INV_X2
    I111 net086 VDD VDD VSS VSS net034 RSn\<7\> net34 DFFRPQN_X3
    I118 net052 VDD VDD VSS VSS net038 RSn\<4\> net34 DFFRPQN_X3
    I116 net046 VDD VDD VSS VSS net034 RSn\<5\> net34 DFFRPQN_X3
    I30 net063 VDD VDD VSS VSS net038 net030 net34 DFFRPQN_X3
    I115 net087 VDD VDD VSS VSS net038 RSn\<6\> net34 DFFRPQN_X3
    I0 net085 VDD VDD VSS VSS net038 net030 net34 DFFRPQN_X3
    I121 net069 VDD VDD VSS VSS net034 RSn\<3\> net34 DFFRPQN_X3
    I64 net065 VDD VDD VSS VSS QSP DLY2_X2
    I12 net080 VDD VDD VSS VSS net050 DLY2_X2
    I11 net083 VDD VDD VSS VSS net080 DLY2_X2
    I29 net030 VDD VDD VSS VSS TIEHI_X1
    I65 net34 VDD VDD VSS VSS net060 INV_X8
.ends SUB5_SEQ_6b
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB5_SEQ_TOP_6b_v2
// View name: schematic
.subckt SUB5_SEQ_TOP_6b_v2 DN\<1\> DN\<2\> DOUT\<5\> DOUT\<4\> DOUT\<3\> \
        DOUT\<2\> DOUT\<1\> DOUT\<0\> DP\<1\> DP\<2\> ENV\<2\> ENV\<3\> \
        ENV\<4\> INITP N_Nch\<5\> N_Nch\<4\> N_Nch\<3\> N_Nch\<2\> \
        N_Nch\<1\> P_Nch\<5\> P_Nch\<4\> P_Nch\<3\> P_Nch\<2\> P_Nch\<1\> \
        QSP RDY\<1\> RDY\<2\> VDD VSS
    I43 CKP\<5\> CKP\<4\> CKP\<3\> CKP\<2\> CKP\<1\> CKP\<0\> DOUT\<5\> \
        DOUT\<4\> DOUT\<3\> DOUT\<2\> DOUT\<1\> DOUT\<0\> DN\<1\> DN\<2\> \
        DP\<1\> DP\<2\> INITP N_Nch\<5\> N_Nch\<4\> N_Nch\<3\> N_Nch\<2\> \
        N_Nch\<1\> P_Nch\<5\> P_Nch\<4\> P_Nch\<3\> P_Nch\<2\> P_Nch\<1\> \
        QSP VDD VSS SUB4_SAR_TOP
    I44 CKP\<5\> CKP\<4\> CKP\<3\> CKP\<2\> CKP\<1\> CKP\<0\> ENV\<2\> \
        ENV\<3\> ENV\<4\> QSP RDY\<1\> RDY\<2\> VDD VSS SUB5_SEQ_6b
.ends SUB5_SEQ_TOP_6b_v2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: NOR3_X4
// View name: schematic
.subckt NOR3_X4 Y VDD VNW VPW VSS A B C
    MMPB p0__2 B p1 VNW slvtpfet w=81n l=14n m=1
    MMPA Y A p0__2 VNW slvtpfet w=81n l=14n m=1
    MMPA_4 Y A p0__3 VNW slvtpfet w=81n l=14n m=1
    MMPB_4 p0__3 B p1 VNW slvtpfet w=81n l=14n m=1
    MMPB_3 p0__4 B p1 VNW slvtpfet w=81n l=14n m=1
    MMPA_3 Y A p0__4 VNW slvtpfet w=81n l=14n m=1
    MMPA_2 Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMPB_2 p0 B p1 VNW slvtpfet w=81n l=14n m=1
    MMPC_2 p1 C VDD VNW slvtpfet w=81n l=14n m=1
    MMPC_3 p1 C VDD VNW slvtpfet w=81n l=14n m=1
    MMPC_4 p1 C VDD VNW slvtpfet w=81n l=14n m=1
    MMPC p1 C VDD VNW slvtpfet w=81n l=14n m=1
    MMNB_2 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_2 Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_3 Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_3 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_4 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_4 Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNC_2 Y C VSS VPW slvtnfet w=81n l=14n m=1
    MMNC_3 Y C VSS VPW slvtnfet w=81n l=14n m=1
    MMNC_4 Y C VSS VPW slvtnfet w=81n l=14n m=1
    MMNC Y C VSS VPW slvtnfet w=81n l=14n m=1
.ends NOR3_X4
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: BUF_X8
// View name: schematic
.subckt BUF_X8 Y VDD VNW VPW VSS A
    I2 Y net027 VSS VPW slvtnfet w=81n l=14n m=8
    I0 net027 A VSS VPW slvtnfet w=81n l=14n m=3
    I1 net027 A VDD VNW slvtpfet w=81n l=14n m=3
    I3 Y net027 VDD VNW slvtpfet w=81n l=14n m=8
.ends BUF_X8
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: NOR2_X2
// View name: schematic
.subckt NOR2_X2 Y VDD VNW VPW VSS A B
    MMPB_2 p0 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPA_2 Y A p0 VNW slvtpfet w=81n l=14n m=1
    MMPB p0__2 B VDD VNW slvtpfet w=81n l=14n m=1
    MMPA Y A p0__2 VNW slvtpfet w=81n l=14n m=1
    MMNB Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNB_2 Y B VSS VPW slvtnfet w=81n l=14n m=1
    MMNA Y A VSS VPW slvtnfet w=81n l=14n m=1
    MMNA_2 Y A VSS VPW slvtnfet w=81n l=14n m=1
.ends NOR2_X2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: SUB3_CLK2
// View name: schematic
.subckt SUB3_CLK2 ENV\<2\> ENV\<3\> ENV\<4\> LAT\<1\> LAT\<2\> QS_DEL \
        RDY\<1\> RDY\<2\> RS\<1\> RS\<2\> VDD VSS
    M20 net095 net0115 VDD VDD slvtpfet w=81n l=14n m=4
    M1 net087 net037 VDD VDD slvtpfet w=81n l=14n m=2
    M15 net099 net054 VDD VDD slvtpfet w=81n l=14n m=2
    M0 net092 ENV\<2\> net087 VDD slvtpfet w=81n l=14n m=2
    I150 net022 net0117 VDD VDD slvtpfet w=81n l=14n m=4
    M4 net092 net0102 net088 VDD slvtpfet w=81n l=14n m=2
    I151 net022 net024 VDD VDD slvtpfet w=81n l=14n m=4
    M12 net084 net089 net093 VDD slvtpfet w=81n l=14n m=2
    M8 net084 ENV\<3\> net099 VDD slvtpfet w=81n l=14n m=2
    M9 net093 net033 VDD VDD slvtpfet w=81n l=14n m=2
    M7 net088 net0109 VDD VDD slvtpfet w=81n l=14n m=2
    I134 net078 VDD VDD VSS VSS net011 net020 net084 NOR3_X4
    I103 RS\<2\> VDD VDD VSS VSS net073 BUF_X8
    I96 RS\<1\> VDD VDD VSS VSS net047 BUF_X8
    I139 net073 VDD VDD VSS VSS net048 net095 NOR2_X2
    I92 net047 VDD VDD VSS VSS net049 net022 NOR2_X2
    I161 net0117 VDD VDD VSS VSS net0120 DLY2_X2
    I160 net0115 VDD VDD VSS VSS net0118 DLY2_X2
    I159 net0120 VDD VDD VSS VSS net039 DLY2_X2
    I158 net0118 VDD VDD VSS VSS net063 DLY2_X2
    I140 net0110 VDD VDD VSS VSS net056 DLY2_X2
    I93 net049 VDD VDD VSS VSS net022 DLY2_X2
    I79 net011 VDD VDD VSS VSS net0103 DLY2_X2
    I78 net029 VDD VDD VSS VSS net017 DLY2_X2
    I136 net020 VDD VDD VSS VSS net058 DLY2_X2
    I116 net064 VDD VDD VSS VSS net072 DLY2_X2
    I99 net048 VDD VDD VSS VSS net095 DLY2_X2
    I119 net033 VDD VDD VSS VSS net077 DLY2_X2
    I122 net059 VDD VDD VSS VSS net033 DLY2_X2
    I141 net0112 VDD VDD VSS VSS net029 DLY2_X2
    I121 net054 VDD VDD VSS VSS net059 DLY2_X2
    I142 net072 VDD VDD VSS VSS net0111 DLY2_X2
    I145 net0103 VDD VDD VSS VSS QS_DEL DLY2_X2
    I144 net0100 VDD VDD VSS VSS RDY\<1\> DLY2_X2
    I127 net0108 VDD VDD VSS VSS net0109 DLY2_X2
    I114 net056 VDD VDD VSS VSS net078 DLY2_X2
    I143 net077 VDD VDD VSS VSS RDY\<2\> DLY2_X2
    I130 net0109 VDD VDD VSS VSS net0100 DLY2_X2
    I126 net037 VDD VDD VSS VSS net0108 DLY2_X2
    M13 net094 net054 VSS VSS slvtnfet w=81n l=14n m=2
    I153 net022 net076 VSS VSS slvtnfet w=81n l=14n m=4
    M14 net084 net089 net094 VSS slvtnfet w=81n l=14n m=2
    M2 net092 net0102 net0101 VSS slvtnfet w=81n l=14n m=2
    M10 net084 ENV\<3\> net0104 VSS slvtnfet w=81n l=14n m=2
    I152 net095 net0114 VSS VSS slvtnfet w=81n l=14n m=4
    M19 VSS net095 VSS VSS slvtnfet w=81n l=14n m=4
    M18 VSS net022 VSS VSS slvtnfet w=81n l=14n m=4
    M11 net0104 net033 VSS VSS slvtnfet w=81n l=14n m=2
    M5 net090 net0109 VSS VSS slvtnfet w=81n l=14n m=2
    M6 net092 ENV\<2\> net090 VSS slvtnfet w=81n l=14n m=2
    M3 net0101 net037 VSS VSS slvtnfet w=81n l=14n m=2
    I135 net058 VDD VDD VSS VSS ENV\<4\> INV_X4
    I105 net024 VDD VDD VSS VSS net017 net052 NAND2_X3
    I113 net039 VDD VDD VSS VSS net078 net040 NAND2_X3
    I117 net063 VDD VDD VSS VSS net0111 net066 NAND2_X3
    I111 net017 VDD VDD VSS VSS net0103 INV_X2
    I107 net052 VDD VDD VSS VSS net0112 INV_X2
    I125 net089 VDD VDD VSS VSS ENV\<3\> INV_X2
    I112 net040 VDD VDD VSS VSS net0110 INV_X2
    I115 net066 VDD VDD VSS VSS net064 INV_X2
    I129 net0102 VDD VDD VSS VSS ENV\<2\> INV_X2
    I128 net0111 VDD VDD VSS VSS net028 INV_X2
    I131 net028 VDD VDD VSS VSS net092 BUF_X2
    I148 net0114 VDD VDD VSS VSS RDY\<2\> BUF_X2
    I147 net076 VDD VDD VSS VSS RDY\<1\> BUF_X2
    I66 LAT\<1\> VDD VDD VSS VSS net097 INV_X16
    I80 LAT\<2\> VDD VDD VSS VSS net055 INV_X16
    I100 net097 VDD VDD VSS VSS net022 BUF_X4
    I110 net055 VDD VDD VSS VSS net095 BUF_X4
.ends SUB3_CLK2
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: Asynch_SAR_ADC_6b_2GSPS
// View name: schematic
.subckt SAR_ADC_6b_2GSPS CLK DOUT\<5\> DOUT\<4\> DOUT\<3\> DOUT\<2\> \
        DOUT\<1\> DOUT\<0\> IN IP REFN REFP VDD VSS
    I11 QE CLK QIP QSN QSP QD VDD VSS SUB3_CLK1
    I18 DN\<1\> DN\<2\> DP\<1\> DP\<2\> ON OP LAT\<1\> LAT\<2\> RDY\<1\> \
        RDY\<2\> RS\<1\> RS\<2\> VDD VSS SUB2_COMP_DUPLEX
    I27 N_Nch\<5\> N_Nch\<4\> N_Nch\<3\> N_Nch\<2\> N_Nch\<1\> P_Nch\<5\> \
        P_Nch\<4\> P_Nch\<3\> P_Nch\<2\> P_Nch\<1\> IN IP ON OP QSN QSP \
        REFN REFP VDD VSS SUB1_CDAC_6b_diff
    I20 DN\<1\> DN\<2\> DOUT\<5\> DOUT\<4\> DOUT\<3\> DOUT\<2\> DOUT\<1\> \
        DOUT\<0\> DP\<1\> DP\<2\> ENV\<2\> ENV\<3\> ENV\<4\> QIP \
        N_Nch\<5\> N_Nch\<4\> N_Nch\<3\> N_Nch\<2\> N_Nch\<1\> P_Nch\<5\> \
        P_Nch\<4\> P_Nch\<3\> P_Nch\<2\> P_Nch\<1\> QE RDY\<1\> RDY\<2\> \
        VDD VSS SUB5_SEQ_TOP_6b_v2
    I10 ENV\<2\> ENV\<3\> ENV\<4\> LAT\<1\> LAT\<2\> QD RDY\<1\> RDY\<2\> \
        RS\<1\> RS\<2\> VDD VSS SUB3_CLK2
.ends SAR_ADC_6b_2GSPS
// End of subcircuit definition.

// Library name: POSH_SPICE_6b2GSPS
// Cell name: TB_ADC
// View name: schematic
xI0 CLK DOUT\<5\> DOUT\<4\> DOUT\<3\> DOUT\<2\> DOUT\<1\> DOUT\<0\> IN IP \
        REFN REFP VDD VSS Asynch_SAR_ADC_6b_2GSPS
xI4\<5\> DOUT\<5\> net09\<0\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI4\<4\> DOUT\<4\> net09\<1\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI4\<3\> DOUT\<3\> net09\<2\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI4\<2\> DOUT\<2\> net09\<3\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI4\<1\> DOUT\<1\> net09\<4\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI4\<0\> DOUT\<0\> net09\<5\> not_gate vlogic_high=1 vlogic_low=0 \
        vtrans=0.4 tdel=0 trise=10p tfall=10p
xI6\<5\> net09\<0\> D\<5\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
xI6\<4\> net09\<1\> D\<4\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
xI6\<3\> net09\<2\> D\<3\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
xI6\<2\> net09\<3\> D\<2\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
xI6\<1\> net09\<4\> D\<1\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
xI6\<0\> net09\<5\> D\<0\> not_gate vlogic_high=1 vlogic_low=0 vtrans=0.4 \
        tdel=0 trise=10p tfall=10p
