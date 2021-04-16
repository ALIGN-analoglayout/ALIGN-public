// Generated for: spectre
// Generated on: May 12 11:46:13 2019
// Design library name: POSH_TI_SAR_zqc_20190501
// Design cell name: chip_core_TI
// Design view name: schematic
simulator lang=spectre
global 0

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: inverter
// View name: schematic
subckt inverter VDD VIN VOUT VSS
    M0 (VOUT VIN VSS VSS) nmos w=900n l=45n m=10
    M1 (VOUT VIN VDD VDD) pmos w=900n l=45n m=35
ends inverter
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: NAND2
// View name: schematic
subckt NAND2 A B VDD VSS D
    M1 (net7 B VSS VSS) nmos w=900n l=45n m=20
    M0 (D A net7 VSS) nmos w=900n l=45n m=20
    M3 (D B VDD VDD) pmos w=900n l=45n m=35
    M2 (D A VDD VDD) pmos w=900n l=45n m=35
ends NAND2
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: DFF_reset
// View name: schematic
subckt DFF_reset CLK D Q Qbar VDD VSS R
    I10 (VDD net015 net026 VSS) inverter
    I7 (VDD R net019 VSS) inverter
    I13 (VDD CLK net013 VSS) inverter
    I12 (net015 net014 VDD VSS net011) NAND2
    I11 (net014 net026 VDD VSS net010) NAND2
    I9 (net019 net023 VDD VSS net015) NAND2
    I8 (net022 net010 VDD VSS net023) NAND2
    I5 (net011 D VDD VSS net022) NAND2
    I3 (Qbar net010 VDD VSS Q) NAND2
    I2 (net011 Q VDD VSS Qbar) NAND2
    I6 (net019 net013 VDD VSS net014) NAND2
ends DFF_reset
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: transmission_gate
// View name: schematic
subckt transmission_gate A B CLK CLKbar VDD VSS
    M6 (A CLK B VSS) nmos w=90n l=45n m=2
    M7 (B CLKbar A VDD) pmos w=90n l=45n m=7
ends transmission_gate
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: comparator_p
// View name: schematic
subckt comparator_p CLKC RDY VDD VINN VINP VOUTN VOUTP VSS
    M10 (VOUTN net16 VSS VSS) nmos w=900n l=45n m=10
    M3 (net16 net9 VSS VSS) nmos w=900n l=45n m=10
    M5 (net16 CLKC VSS VSS) nmos w=900n l=45n m=5
    M4 (net9 CLKC VSS VSS) nmos w=900n l=45n m=5
    M7 (VOUTP net9 VSS VSS) nmos w=900n l=45n m=10
    M6 (net9 net16 VSS VSS) nmos w=900n l=45n m=10
    M9 (VOUTN net16 VDD VDD) pmos w=900n l=45n m=35
    M0 (net12 CLKC VDD VDD) pmos w=900n l=45n m=70
    M2 (net16 VINN net12 VDD) pmos w=900n l=45n m=20
    M1 (net9 VINP net12 VDD) pmos w=900n l=45n m=20
    M8 (VOUTP net9 VDD VDD) pmos w=900n l=45n m=35
    I1 (VOUTP VOUTN VDD VSS RDY) NAND2
ends comparator_p
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: buffer
// View name: schematic
subckt buffer VDD VIN VOUT VSS
    M2 (VOUT net40 VSS VSS) nmos w=900.0n l=45n m=10
    M0 (net40 VIN VSS VSS) nmos w=900.0n l=45n m=10
    M3 (VOUT net40 VDD VDD) pmos w=900n l=45n m=35
    M1 (net40 VIN VDD VDD) pmos w=900n l=45n m=35
ends buffer
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: Latch
// View name: schematic
subckt Latch CLK D Q Qbar VDD VSS
    I4 (VDD D net13 VSS) inverter
    I3 (Q net010 VDD VSS Qbar) NAND2
    I2 (net011 Qbar VDD VSS Q) NAND2
    I1 (CLK net13 VDD VSS net010) NAND2
    I0 (D CLK VDD VSS net011) NAND2
ends Latch
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: DFF
// View name: schematic
subckt DFF CLK D Q Qbar VDD VSS
    I6 (CLK net013 Q Qbar VDD VSS) Latch
    I5 (net012 D net013 net014 VDD VSS) Latch
    I7 (VDD CLK net012 VSS) inverter
ends DFF
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: DAC_ctrl_logic
// View name: schematic
subckt DAC_ctrl_logic B CLK OUT V2DAC VDD VREF VSS
    I2 (B net7 VDD VSS net015) NAND2
    I5 (VDD net015 net9 VSS) inverter
    I4 (VDD CLK net7 VSS) buffer
    M0 (V2DAC net9 VSS VSS) nmos w=900.0n l=45n m=10
    I0 (CLK OUT B net11 VDD VSS) DFF
    M1 (V2DAC net9 VREF VREF) pmos w=900n l=45n m=35
ends DAC_ctrl_logic
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: NOR3
// View name: schematic
subckt NOR3 A B C D VDD VSS
    M4 (D C VSS VSS) nmos w=900n l=45n m=10
    M0 (D B VSS VSS) nmos w=900n l=45n m=10
    M1 (D A VSS VSS) nmos w=900n l=45n m=10
    M5 (D C net23 VDD) pmos w=900n l=45n m=105
    M3 (net23 B net24 VDD) pmos w=900n l=45n m=105
    M2 (net24 A VDD VDD) pmos w=900n l=45n m=105
ends NOR3
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: async_logic
// View name: schematic
subckt async_logic CLK\<0\> CLK\<1\> CLK\<2\> CLK\<3\> CLK\<4\> CLK\<5\> \
        CLK\<6\> CLK\<7\> CLKC CLKS RDY VDD VSS
    I19 (CLKS RDY CLK\<7\> net01 VDD VSS) NOR3
    I20 (VDD net01 net016 VSS) inverter
    I21 (VDD net016 CLKC VSS) buffer
    I9 (RDY CLK\<6\> CLK\<7\> net5 VDD VSS CLKS) DFF_reset
    I8 (RDY CLK\<5\> CLK\<6\> net12 VDD VSS CLKS) DFF_reset
    I7 (RDY CLK\<4\> CLK\<5\> net19 VDD VSS CLKS) DFF_reset
    I6 (RDY CLK\<3\> CLK\<4\> net26 VDD VSS CLKS) DFF_reset
    I5 (RDY CLK\<2\> CLK\<3\> net33 VDD VSS CLKS) DFF_reset
    I4 (RDY CLK\<1\> CLK\<2\> net40 VDD VSS CLKS) DFF_reset
    I2 (RDY VDD CLK\<0\> net52 VDD VSS CLKS) DFF_reset
    I3 (RDY CLK\<0\> CLK\<1\> net47 VDD VSS CLKS) DFF_reset
ends async_logic
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: SAR_logic
// View name: schematic
subckt SAR_logic B\<0\> B\<1\> B\<2\> B\<3\> B\<4\> B\<5\> B\<6\> B\<7\> \
        Bbar\<0\> Bbar\<1\> Bbar\<2\> Bbar\<3\> Bbar\<4\> Bbar\<5\> \
        Bbar\<6\> Bbar\<7\> CLKC CLKS OUT_N OUT_P RDY V2DAC_N\<0\> \
        V2DAC_N\<1\> V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> \
        V2DAC_N\<6\> V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> \
        V2DAC_P\<3\> V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> \
        VDD VREF VSS CLK\<0\> CLK\<1\> CLK\<2\> CLK\<3\> CLK\<4\> CLK\<5\> \
        CLK\<6\> CLK\<7\>
    I10\<0\> (Bbar\<0\> CLK\<0\> OUT_N V2DAC_N\<0\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<1\> (Bbar\<1\> CLK\<1\> OUT_N V2DAC_N\<1\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<2\> (Bbar\<2\> CLK\<2\> OUT_N V2DAC_N\<2\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<3\> (Bbar\<3\> CLK\<3\> OUT_N V2DAC_N\<3\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<4\> (Bbar\<4\> CLK\<4\> OUT_N V2DAC_N\<4\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<5\> (Bbar\<5\> CLK\<5\> OUT_N V2DAC_N\<5\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<6\> (Bbar\<6\> CLK\<6\> OUT_N V2DAC_N\<6\> VDD VREF VSS) \
        DAC_ctrl_logic
    I10\<7\> (Bbar\<7\> CLK\<7\> OUT_N V2DAC_N\<7\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<0\> (B\<0\> CLK\<0\> OUT_P V2DAC_P\<0\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<1\> (B\<1\> CLK\<1\> OUT_P V2DAC_P\<1\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<2\> (B\<2\> CLK\<2\> OUT_P V2DAC_P\<2\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<3\> (B\<3\> CLK\<3\> OUT_P V2DAC_P\<3\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<4\> (B\<4\> CLK\<4\> OUT_P V2DAC_P\<4\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<5\> (B\<5\> CLK\<5\> OUT_P V2DAC_P\<5\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<6\> (B\<6\> CLK\<6\> OUT_P V2DAC_P\<6\> VDD VREF VSS) \
        DAC_ctrl_logic
    I2\<7\> (B\<7\> CLK\<7\> OUT_P V2DAC_P\<7\> VDD VREF VSS) \
        DAC_ctrl_logic
    I0 (CLK\<0\> CLK\<1\> CLK\<2\> CLK\<3\> CLK\<4\> CLK\<5\> CLK\<6\> \
        CLK\<7\> CLKC CLKS RDY VDD VSS) async_logic
ends SAR_logic
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: CDAC
// View name: schematic
subckt CDAC S\<0\> S\<1\> S\<2\> S\<3\> S\<4\> S\<5\> S\<6\> S\<7\> TOP \
        ground
    C10 (TOP ground) capacitor c=3.90625f
    C7 (TOP S\<7\>) capacitor c=3.90625f
    C6 (TOP S\<6\>) capacitor c=7.8125f
    C5 (TOP S\<5\>) capacitor c=15.625f
    C4 (TOP S\<4\>) capacitor c=31.25f
    C3 (TOP S\<3\>) capacitor c=62.5f
    C2 (TOP S\<2\>) capacitor c=125f
    C1 (TOP S\<1\>) capacitor c=250f
    C0 (TOP S\<0\>) capacitor c=500.0f
ends CDAC
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: clk_doubler
// View name: schematic
subckt clk_doubler VDD VIN VOUT VSS
    C1 (VOUT net5) capacitor c=2.5p m=3 ic=0
    C0 (VOUTb VIN) capacitor c=2.5p m=3 ic=0
    M0 (VDD VOUTb VOUT VSS) nmos w=600.0n l=45n m=10
    M18 (VDD VOUT VOUTb VSS) nmos w=600.0n l=45n m=10
    I0 (VDD VIN net5 VSS) inverter
ends clk_doubler
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: bootstrap
// View name: schematic
subckt bootstrap OUT VDD VSS clk clkb clkb_high IN
    M10 (net01 clk IN VSS) nmos w=900n l=45n m=20
    M11 (net012 clk IN VSS) nmos w=900.0n l=45n m=40
    M6 (VSS clkb net011 VSS) nmos w=900.0n l=45n m=1
    M4 (OUT net011 IN VSS) nmos w=900.0n l=45n m=10
    M1q (net01 clkb VSS VSS) nmos w=900.0n l=45n m=50
    M0 (VDD clkb_high net8 VSS) nmos w=900.0n l=45n m=1
    C0 (net8 net01) capacitor c=20p ic=1.1
    M12 (IN clkb net01 VDD) pmos w=900n l=45n m=20
    M7 (IN clkb net012 VDD) pmos w=900.0n l=45n m=40
    M13 (net012 clk VDD VDD) pmos w=900.0n l=45n m=20
    M2 (net011 net012 net8 net8) pmos w=900n l=45n m=1
ends bootstrap
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: bootstrap_diff
// View name: schematic
subckt bootstrap_diff CLK CLKbar INN INP VDD VOUTN VOUTP VSS
    I18 (VDD CLK net6 VSS) clk_doubler
    I19 (VDD CLK net5 VSS) clk_doubler
    I14 (VOUTP VDD VSS CLK CLKbar net6 INP) bootstrap
    I10 (VOUTN VDD VSS CLK CLKbar net5 INN) bootstrap
ends bootstrap_diff
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: SH
// View name: schematic
subckt SH CLK CLKbar INN INP OUTN OUTP V2DAC_N\<0\> V2DAC_N\<1\> \
        V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> \
        V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> \
        V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VDD VSS
    I2 (V2DAC_N\<0\> V2DAC_N\<1\> V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> \
        V2DAC_N\<5\> V2DAC_N\<6\> V2DAC_N\<7\> OUTN VSS) CDAC
    I1 (V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> V2DAC_P\<4\> \
        V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> OUTP VSS) CDAC
    I0 (CLK CLKbar INN INP VDD OUTN OUTP VSS) bootstrap_diff
ends SH
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: chip_core
// View name: schematic
subckt chip_core B\<0\> B\<1\> B\<2\> B\<3\> B\<4\> B\<5\> B\<6\> B\<7\> \
        Bbar\<0\> Bbar\<1\> Bbar\<2\> Bbar\<3\> Bbar\<4\> Bbar\<5\> \
        Bbar\<6\> Bbar\<7\> CLKC CLKS RDY V2DAC_N\<0\> V2DAC_N\<1\> \
        V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> \
        V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> \
        V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VCMP_N VCMP_P \
        VDD VIN_N VIN_P VREF VSH_N VSH_P VSS CLK\<0\> CLK\<1\> CLK\<2\> \
        CLK\<3\> CLK\<4\> CLK\<5\> CLK\<6\> CLK\<7\>
    I1 (CLKC RDY VDD VSH_N VSH_P VCMP_N VCMP_P VSS) comparator_p
    I2 (B\<0\> B\<1\> B\<2\> B\<3\> B\<4\> B\<5\> B\<6\> B\<7\> Bbar\<0\> \
        Bbar\<1\> Bbar\<2\> Bbar\<3\> Bbar\<4\> Bbar\<5\> Bbar\<6\> \
        Bbar\<7\> CLKC CLKS VCMP_N VCMP_P RDY V2DAC_N\<0\> V2DAC_N\<1\> \
        V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> \
        V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> \
        V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VDD VREF VSS \
        CLK\<0\> CLK\<1\> CLK\<2\> CLK\<3\> CLK\<4\> CLK\<5\> CLK\<6\> \
        CLK\<7\>) SAR_logic
    I6 (VDD CLKS CLKSbar VSS) inverter
    I0 (CLKS CLKSbar VIN_N VIN_P VSH_N VSH_P V2DAC_N\<0\> V2DAC_N\<1\> \
        V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> \
        V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> \
        V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VDD VSS) SH
ends chip_core
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: chip_core_all
// View name: schematic
subckt chip_core_all B\<0\> B\<1\> B\<2\> B\<3\> B\<4\> B\<5\> B\<6\> \
        B\<7\> Bbar\<0\> Bbar\<1\> Bbar\<2\> Bbar\<3\> Bbar\<4\> Bbar\<5\> \
        Bbar\<6\> Bbar\<7\> CLKC CLKS RDY V2DAC_N\<0\> V2DAC_N\<1\> \
        V2DAC_N\<2\> V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> \
        V2DAC_N\<7\> V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> \
        V2DAC_P\<4\> V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VCMP_N VCMP_P \
        VDD VIN_N VIN_P VREF VSH_N VSH_P VSS CLK\<0\> CLK\<1\> CLK\<2\> \
        CLK\<3\> CLK\<4\> CLK\<5\> CLK\<6\> CLK\<7\> OUTCODE\<0\> \
        OUTCODE\<1\> OUTCODE\<2\> OUTCODE\<3\> OUTCODE\<4\> OUTCODE\<5\> \
        OUTCODE\<6\> OUTCODE\<7\> RESET_OUTCODE
    I34\<0\> (CLKS B\<0\> OUTCODE\<0\> net22\<0\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<1\> (CLKS B\<1\> OUTCODE\<1\> net22\<1\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<2\> (CLKS B\<2\> OUTCODE\<2\> net22\<2\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<3\> (CLKS B\<3\> OUTCODE\<3\> net22\<3\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<4\> (CLKS B\<4\> OUTCODE\<4\> net22\<4\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<5\> (CLKS B\<5\> OUTCODE\<5\> net22\<5\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<6\> (CLKS B\<6\> OUTCODE\<6\> net22\<6\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I34\<7\> (CLKS B\<7\> OUTCODE\<7\> net22\<7\> VDD VSS RESET_OUTCODE) \
        DFF_reset
    I0 (B\<0\> B\<1\> B\<2\> B\<3\> B\<4\> B\<5\> B\<6\> B\<7\> Bbar\<0\> \
        Bbar\<1\> Bbar\<2\> Bbar\<3\> Bbar\<4\> Bbar\<5\> Bbar\<6\> \
        Bbar\<7\> CLKC CLKS RDY V2DAC_N\<0\> V2DAC_N\<1\> V2DAC_N\<2\> \
        V2DAC_N\<3\> V2DAC_N\<4\> V2DAC_N\<5\> V2DAC_N\<6\> V2DAC_N\<7\> \
        V2DAC_P\<0\> V2DAC_P\<1\> V2DAC_P\<2\> V2DAC_P\<3\> V2DAC_P\<4\> \
        V2DAC_P\<5\> V2DAC_P\<6\> V2DAC_P\<7\> VCMP_N VCMP_P VDD VIN_N \
        VIN_P VREF VSH_N VSH_P VSS CLK\<0\> CLK\<1\> CLK\<2\> CLK\<3\> \
        CLK\<4\> CLK\<5\> CLK\<6\> CLK\<7\>) chip_core
ends chip_core_all
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: buffer_delay
// View name: schematic
subckt buffer_delay VDD VIN VOUT VSS
    M2 (VOUT net40 VSS VSS) nmos w=90.0n l=45n m=2
    M0 (net40 VIN VSS VSS) nmos w=90n l=45n m=2
    M3 (VOUT net40 VDD VDD) pmos w=90n l=45n m=7
    M1 (net40 VIN VDD VDD) pmos w=90n l=45n m=7
ends buffer_delay
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: DFF_set
// View name: schematic
subckt DFF_set CLK D Q Qbar VDD VSS S
    I14 (VDD D net025 VSS) inverter
    I10 (VDD net015 net026 VSS) inverter
    I7 (VDD S net019 VSS) inverter
    I13 (VDD CLK net013 VSS) inverter
    I12 (net015 net014 VDD VSS net011) NAND2
    I11 (net014 net026 VDD VSS net010) NAND2
    I9 (net019 net023 VDD VSS net015) NAND2
    I8 (net022 net010 VDD VSS net023) NAND2
    I5 (net011 net025 VDD VSS net022) NAND2
    I3 (Q net010 VDD VSS Qbar) NAND2
    I2 (net011 Qbar VDD VSS Q) NAND2
    I6 (net019 net013 VDD VSS net014) NAND2
ends DFF_set
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: clk_gen_TI
// View name: schematic
subckt clk_gen_TI CLK CLK_DIV\<0\> CLK_DIV\<1\> CLK_DIV\<2\> CLK_DIV\<3\> \
        INITIALIZE VDD VSS
    I5 (CLK CLK_DIV_inter\<2\> CLK_DIV_inter\<3\> net3 VDD VSS INITIALIZE) \
        DFF_reset
    I4 (CLK CLK_DIV_inter\<1\> CLK_DIV_inter\<2\> net4 VDD VSS INITIALIZE) \
        DFF_reset
    I3 (CLK CLK_DIV_inter\<0\> CLK_DIV_inter\<1\> net5 VDD VSS INITIALIZE) \
        DFF_reset
    I13\<0\> (VDD net010\<0\> CLK_DIV\<0\> VSS) inverter
    I13\<1\> (VDD net010\<1\> CLK_DIV\<1\> VSS) inverter
    I13\<2\> (VDD net010\<2\> CLK_DIV\<2\> VSS) inverter
    I13\<3\> (VDD net010\<3\> CLK_DIV\<3\> VSS) inverter
    I11\<0\> (VDD CLK_DIV_inter\<0\> net012\<0\> VSS) buffer_delay
    I11\<1\> (VDD CLK_DIV_inter\<1\> net012\<1\> VSS) buffer_delay
    I11\<2\> (VDD CLK_DIV_inter\<2\> net012\<2\> VSS) buffer_delay
    I11\<3\> (VDD CLK_DIV_inter\<3\> net012\<3\> VSS) buffer_delay
    I2 (CLK CLK_DIV_inter\<3\> CLK_DIV_inter\<0\> net6 VDD VSS INITIALIZE) \
        DFF_set
    I10\<0\> (CLK_DIV_inter\<0\> net012\<0\> VDD VSS net010\<0\>) NAND2
    I10\<1\> (CLK_DIV_inter\<1\> net012\<1\> VDD VSS net010\<1\>) NAND2
    I10\<2\> (CLK_DIV_inter\<2\> net012\<2\> VDD VSS net010\<2\>) NAND2
    I10\<3\> (CLK_DIV_inter\<3\> net012\<3\> VDD VSS net010\<3\>) NAND2
ends clk_gen_TI
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: chip_core_TI
// View name: schematic
I122\<0\> (CLK_IN TIADC_OUTCODE\<0\> OUTCODE\<0\> net013\<0\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<1\> (CLK_IN TIADC_OUTCODE\<1\> OUTCODE\<1\> net013\<1\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<2\> (CLK_IN TIADC_OUTCODE\<2\> OUTCODE\<2\> net013\<2\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<3\> (CLK_IN TIADC_OUTCODE\<3\> OUTCODE\<3\> net013\<3\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<4\> (CLK_IN TIADC_OUTCODE\<4\> OUTCODE\<4\> net013\<4\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<5\> (CLK_IN TIADC_OUTCODE\<5\> OUTCODE\<5\> net013\<5\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<6\> (CLK_IN TIADC_OUTCODE\<6\> OUTCODE\<6\> net013\<6\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I122\<7\> (CLK_IN TIADC_OUTCODE\<7\> OUTCODE\<7\> net013\<7\> VDD VSS \
        RESET_OUTCODE) DFF_reset
I120\<0\> (VDD CLKS\<0\> CLKSbar\<0\> VSS) inverter
I120\<1\> (VDD CLKS\<1\> CLKSbar\<1\> VSS) inverter
I120\<2\> (VDD CLKS\<2\> CLKSbar\<2\> VSS) inverter
I120\<3\> (VDD CLKS\<3\> CLKSbar\<3\> VSS) inverter
I116\<0\> (OUTCODE0\<0\> TIADC_OUTCODE\<0\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<1\> (OUTCODE0\<1\> TIADC_OUTCODE\<1\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<2\> (OUTCODE0\<2\> TIADC_OUTCODE\<2\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<3\> (OUTCODE0\<3\> TIADC_OUTCODE\<3\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<4\> (OUTCODE0\<4\> TIADC_OUTCODE\<4\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<5\> (OUTCODE0\<5\> TIADC_OUTCODE\<5\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<6\> (OUTCODE0\<6\> TIADC_OUTCODE\<6\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I116\<7\> (OUTCODE0\<7\> TIADC_OUTCODE\<7\> CLKS\<0\> CLKSbar\<0\> VDD \
        VSS) transmission_gate
I119\<0\> (OUTCODE3\<0\> TIADC_OUTCODE\<0\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<1\> (OUTCODE3\<1\> TIADC_OUTCODE\<1\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<2\> (OUTCODE3\<2\> TIADC_OUTCODE\<2\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<3\> (OUTCODE3\<3\> TIADC_OUTCODE\<3\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<4\> (OUTCODE3\<4\> TIADC_OUTCODE\<4\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<5\> (OUTCODE3\<5\> TIADC_OUTCODE\<5\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<6\> (OUTCODE3\<6\> TIADC_OUTCODE\<6\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I119\<7\> (OUTCODE3\<7\> TIADC_OUTCODE\<7\> CLKS\<3\> CLKSbar\<3\> VDD \
        VSS) transmission_gate
I118\<0\> (OUTCODE2\<0\> TIADC_OUTCODE\<0\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<1\> (OUTCODE2\<1\> TIADC_OUTCODE\<1\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<2\> (OUTCODE2\<2\> TIADC_OUTCODE\<2\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<3\> (OUTCODE2\<3\> TIADC_OUTCODE\<3\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<4\> (OUTCODE2\<4\> TIADC_OUTCODE\<4\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<5\> (OUTCODE2\<5\> TIADC_OUTCODE\<5\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<6\> (OUTCODE2\<6\> TIADC_OUTCODE\<6\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I118\<7\> (OUTCODE2\<7\> TIADC_OUTCODE\<7\> CLKS\<2\> CLKSbar\<2\> VDD \
        VSS) transmission_gate
I117\<0\> (OUTCODE1\<0\> TIADC_OUTCODE\<0\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<1\> (OUTCODE1\<1\> TIADC_OUTCODE\<1\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<2\> (OUTCODE1\<2\> TIADC_OUTCODE\<2\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<3\> (OUTCODE1\<3\> TIADC_OUTCODE\<3\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<4\> (OUTCODE1\<4\> TIADC_OUTCODE\<4\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<5\> (OUTCODE1\<5\> TIADC_OUTCODE\<5\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<6\> (OUTCODE1\<6\> TIADC_OUTCODE\<6\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I117\<7\> (OUTCODE1\<7\> TIADC_OUTCODE\<7\> CLKS\<1\> CLKSbar\<1\> VDD \
        VSS) transmission_gate
I95 (B3\<0\> B3\<1\> B3\<2\> B3\<3\> B3\<4\> B3\<5\> B3\<6\> B3\<7\> \
        B3bar\<0\> B3bar\<1\> B3bar\<2\> B3bar\<3\> B3bar\<4\> B3bar\<5\> \
        B3bar\<6\> B3bar\<7\> CLKC\<3\> CLKS\<3\> RDY3 V2DAC_N3\<0\> \
        V2DAC_N3\<1\> V2DAC_N3\<2\> V2DAC_N3\<3\> V2DAC_N3\<4\> \
        V2DAC_N3\<5\> V2DAC_N3\<6\> V2DAC_N3\<7\> V2DAC_P3\<0\> \
        V2DAC_P3\<1\> V2DAC_P3\<2\> V2DAC_P3\<3\> V2DAC_P3\<4\> \
        V2DAC_P3\<5\> V2DAC_P3\<6\> V2DAC_P3\<7\> VCMP_N3 VCMP_P3 VDD \
        VIN_N VIN_P VREF VSH_N3 VSH_P3 VSS CLK3\<0\> CLK3\<1\> CLK3\<2\> \
        CLK3\<3\> CLK3\<4\> CLK3\<5\> CLK3\<6\> CLK3\<7\> OUTCODE3\<0\> \
        OUTCODE3\<1\> OUTCODE3\<2\> OUTCODE3\<3\> OUTCODE3\<4\> \
        OUTCODE3\<5\> OUTCODE3\<6\> OUTCODE3\<7\> RESET_OUTCODE) \
        chip_core_all
I72 (B2\<0\> B2\<1\> B2\<2\> B2\<3\> B2\<4\> B2\<5\> B2\<6\> B2\<7\> \
        B2bar\<0\> B2bar\<1\> B2bar\<2\> B2bar\<3\> B2bar\<4\> B2bar\<5\> \
        B2bar\<6\> B2bar\<7\> CLKC\<2\> CLKS\<2\> RDY\<2\> V2DAC_N2\<0\> \
        V2DAC_N2\<1\> V2DAC_N2\<2\> V2DAC_N2\<3\> V2DAC_N2\<4\> \
        V2DAC_N2\<5\> V2DAC_N2\<6\> V2DAC_N2\<7\> V2DAC_P2\<0\> \
        V2DAC_P2\<1\> V2DAC_P2\<2\> V2DAC_P2\<3\> V2DAC_P2\<4\> \
        V2DAC_P2\<5\> V2DAC_P2\<6\> V2DAC_P2\<7\> VCMP_N2 VCMP_P2 VDD \
        VIN_N VIN_P VREF VSH_N2 VSH_P2 VSS CLK2\<0\> CLK2\<1\> CLK2\<2\> \
        CLK2\<3\> CLK2\<4\> CLK2\<5\> CLK2\<6\> CLK2\<7\> OUTCODE2\<0\> \
        OUTCODE2\<1\> OUTCODE2\<2\> OUTCODE2\<3\> OUTCODE2\<4\> \
        OUTCODE2\<5\> OUTCODE2\<6\> OUTCODE2\<7\> RESET_OUTCODE) \
        chip_core_all
I49 (B1\<0\> B1\<1\> B1\<2\> B1\<3\> B1\<4\> B1\<5\> B1\<6\> B1\<7\> \
        B1bar\<0\> B1bar\<1\> B1bar\<2\> B1bar\<3\> B1bar\<4\> B1bar\<5\> \
        B1bar\<6\> B1bar\<7\> CLKC\<1\> CLKS\<1\> RDY\<1\> V2DAC_N1\<0\> \
        V2DAC_N1\<1\> V2DAC_N1\<2\> V2DAC_N1\<3\> V2DAC_N1\<4\> \
        V2DAC_N1\<5\> V2DAC_N1\<6\> V2DAC_N1\<7\> V2DAC_P1\<0\> \
        V2DAC_P1\<1\> V2DAC_P1\<2\> V2DAC_P1\<3\> V2DAC_P1\<4\> \
        V2DAC_P1\<5\> V2DAC_P1\<6\> V2DAC_P1\<7\> VCMP_N1 VCMP_P1 VDD \
        VIN_N VIN_P VREF VSH_N1 VSH_P1 VSS CLK1\<0\> CLK1\<1\> CLK1\<2\> \
        CLK1\<3\> CLK1\<4\> CLK1\<5\> CLK1\<6\> CLK1\<7\> OUTCODE1\<0\> \
        OUTCODE1\<1\> OUTCODE1\<2\> OUTCODE1\<3\> OUTCODE1\<4\> \
        OUTCODE1\<5\> OUTCODE1\<6\> OUTCODE1\<7\> RESET_OUTCODE) \
        chip_core_all
I0 (B0\<0\> B0\<1\> B0\<2\> B0\<3\> B0\<4\> B0\<5\> B0\<6\> B0\<7\> \
        B0bar\<0\> B0bar\<1\> B0bar\<2\> B0bar\<3\> B0bar\<4\> B0bar\<5\> \
        B0bar\<6\> B0bar\<7\> CLKC\<0\> CLKS\<0\> RDY\<0\> V2DAC_N0\<0\> \
        V2DAC_N0\<1\> V2DAC_N0\<2\> V2DAC_N0\<3\> V2DAC_N0\<4\> \
        V2DAC_N0\<5\> V2DAC_N0\<6\> V2DAC_N0\<7\> V2DAC_P0\<0\> \
        V2DAC_P0\<1\> V2DAC_P0\<2\> V2DAC_P0\<3\> V2DAC_P0\<4\> \
        V2DAC_P0\<5\> V2DAC_P0\<6\> V2DAC_P0\<7\> VCMP_N0 VCMP_P0 VDD \
        VIN_N VIN_P VREF VSH_N0 VSH_P0 VSS CLK0\<0\> CLK0\<1\> CLK0\<2\> \
        CLK0\<3\> CLK0\<4\> CLK0\<5\> CLK0\<6\> CLK0\<7\> OUTCODE0\<0\> \
        OUTCODE0\<1\> OUTCODE0\<2\> OUTCODE0\<3\> OUTCODE0\<4\> \
        OUTCODE0\<5\> OUTCODE0\<6\> OUTCODE0\<7\> RESET_OUTCODE) \
        chip_core_all
I34 (CLK_IN CLKS\<0\> CLKS\<1\> CLKS\<2\> CLKS\<3\> INITIALIZE VDD VSS) \
        clk_gen_TI
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
