// Generated for: spectre
// Generated on: May 12 11:44:16 2019
// Design library name: POSH_TI_SAR_zqc_20190501
// Design cell name: chip_core_all
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
    C10 (TOP ground) capacitor cap=3.90625f
    C7 (TOP S\<7\>) capacitor cap=3.90625f
    C6 (TOP S\<6\>) capacitor cap=7.8125f
    C5 (TOP S\<5\>) capacitor cap=15.625f
    C4 (TOP S\<4\>) capacitor cap=31.25f
    C3 (TOP S\<3\>) capacitor cap=62.5f
    C2 (TOP S\<2\>) capacitor cap=125f
    C1 (TOP S\<1\>) capacitor cap=250f
    C0 (TOP S\<0\>) capacitor cap=500.0f
ends CDAC
// End of subcircuit definition.

// Library name: POSH_TI_SAR_zqc_20190501
// Cell name: clk_doubler
// View name: schematic
subckt clk_doubler VDD VIN VOUT VSS
    C1 (VOUT net5) capacitor cap=2.5p m=3 ic=0
    C0 (VOUTb VIN) capacitor cap=2.5p m=3 ic=0
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
    C0 (net8 net01) capacitor cap=20p ic=1.1
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
