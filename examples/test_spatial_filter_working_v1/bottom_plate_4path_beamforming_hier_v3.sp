.subckt bottom_plate_4path_beamforming_hier_v3 CLK_X1_P CLK_X1_M CLK_X2_P CLK_X2_M CLK_X3_P CLK_X3_M CLK_X4_P CLK_X4_M OUT_P OUT_M VCMBIAS VDDA VSSA X1_P X1_M X2_P X2_M X3_P X3_M X4_P X4_M 
XI1 CLK_X1_P CLK_X1_M CLK_X2_P CLK_X2_M CLK_X3_P CLK_X3_M CLK_X4_P CLK_X4_M OUT_P OUT_M VCMBIAS VDDA VSSA X1_P X1_M X2_P X2_M X3_P X3_M X4_P X4_M bottom_plate_4path_beamforming 
.ends

.subckt TIA_1 IN_P IN_M OUT_P OUT_M VDDA VSSA
    M1 OUT_P IN_M VSSA VSSA nch_lvt l=400n w=64.0u m=1 nf=8 
    M0 OUT_M IN_P VSSA VSSA nch_lvt l=400n w=64.0u m=1 nf=8 
    M5 net13 OUT_P VDDA VDDA pch l=200n w=32.0u m=1 nf=8 
    M4 net13 OUT_M VDDA VDDA pch l=200n w=32.0u m=1 nf=8 
    M3 OUT_P IN_M net13 net13 pch l=200n w=192u m=1 nf=32 
    M2 OUT_M IN_P net13 net13 pch l=200n w=192u m=1 nf=32 
.ends TIA_1

.subckt bottom_plate_4path_beamforming CLK_X1_P CLK_X1_M CLK_X2_P CLK_X2_M CLK_X3_P CLK_X3_M CLK_X4_P CLK_X4_M OUT_P OUT_M VCMBIAS VDDA VSSA X1_P X1_M X2_P X2_M X3_P X3_M X4_P X4_M
    M15 X4_M CLK_X4_P X4_P_IN_M X4_P_IN_M nmos_rf l=60n w=2u nf=16 
    M14 X3_M CLK_X3_P X3_P_IN_M X3_P_IN_M nmos_rf l=60n w=2u nf=16 
    M13 X2_M CLK_X2_P X2_P_IN_M X2_P_IN_M nmos_rf l=60n w=2u nf=16 
    M12 X1_M CLK_X1_P X1_P_IN_M X1_P_IN_M nmos_rf l=60n w=2u nf=16 
    M11 X4_P CLK_X4_M X4_P_IN_M X4_P_IN_M nmos_rf l=60n w=2u nf=16 
    M10 X3_P CLK_X3_M X3_P_IN_M X3_P_IN_M nmos_rf l=60n w=2u nf=16 
    M9 X2_P CLK_X2_M X2_P_IN_M X2_P_IN_M nmos_rf l=60n w=2u nf=16 
    M8 X1_P CLK_X1_M X1_P_IN_M X1_P_IN_M nmos_rf l=60n w=2u nf=16 
    M7 X4_M CLK_X4_M X4_P_IN_P X4_P_IN_P nmos_rf l=60n w=2u nf=16 
    M6 X3_M CLK_X3_M X3_P_IN_P X3_P_IN_P nmos_rf l=60n w=2u nf=16 
    M5 X2_M CLK_X2_M X2_P_IN_P X2_P_IN_P nmos_rf l=60n w=2u nf=16 
    M4 X1_M CLK_X1_M X1_P_IN_P X1_P_IN_P nmos_rf l=60n w=2u nf=16 
    M3 X4_P CLK_X4_P X4_P_IN_P X4_P_IN_P nmos_rf l=60n w=2u nf=16 
    M2 X3_P CLK_X3_P X3_P_IN_P X3_P_IN_P nmos_rf l=60n w=2u nf=16 
    M1 X2_P CLK_X2_P X2_P_IN_P X2_P_IN_P nmos_rf l=60n w=2u nf=16 
    M0 X1_P CLK_X1_P X1_P_IN_P X1_P_IN_P nmos_rf l=60n w=2u nf=16 
R18  IN_P OUT_M  rppolys res=1 l=10u w=1u m=1 
R16  IN_M OUT_P  rppolys res=1 l=10u w=1u m=1 


R11 X4_P_IN_M IN_M  rppolys res=1 l=14.0u w=1u m=1 

R10 X3_P_IN_M IN_M  rppolys res=1 l=14.0u w=1u m=1 

R9 X2_P_IN_M IN_M  rppolys res=1 l=14.0u w=1u m=1 

R8 X1_P_IN_M IN_M  rppolys res=1 l=14.0u w=1u m=1 

R3 X4_P_IN_P IN_P  rppolys res=1 l=14.0u w=1u m=1 

R2 X3_P_IN_P IN_P  rppolys res=1 l=14.0u w=1u m=1 

R1 X2_P_IN_P IN_P  rppolys res=1 l=14.0u w=1u m=1 

R0 X1_P_IN_P IN_P  rppolys res=1 l=14.0u w=1u m=1 

    C8 IN_P OUT_M mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C9 IN_M OUT_P mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C4 X1_P_IN_M VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C5 X2_P_IN_M VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C7 X4_P_IN_M VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C6 X3_P_IN_M VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C2 X3_P_IN_P VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C3 X4_P_IN_P VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C1 X1_P_IN_P VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    C0 X2_P_IN_P VCMBIAS mimcap_sin cap=10f lt=32.0u wt=32.0u mimflag=3 
    XI0 IN_P IN_M OUT_P OUT_M VDDA VSSA TIA_1
.ends bottom_plate_4path_beamforming


