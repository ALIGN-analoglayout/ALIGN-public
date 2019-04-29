
// Library name: LNA_qmeng
// Cell name: LNA_QM_CORE
// View name: schematic
R5 (net011 VAUX VDD) rppolywo_rf l=6u w=500n m=1 mismatchflag=0
R4 (net063 SF_BIAS VDD) rppolywo_rf l=6u w=500n m=1 mismatchflag=0
R10 (net0252 VMAIN VDD) rppolywo_rf l=6u w=500n m=1 mismatchflag=0
R3 (net033 SF_BIAS VDD) rppolywo_rf l=6u w=500n m=1 mismatchflag=0
C12 (net0252 VSS VSS) mimcap_um_sin_rf lt=16.0u wt=16.0u m=1 mimflag=3 \
        mismatchflag=0
C9 (net0252 VSS VSS) mimcap_um_sin_rf lt=16.0u wt=16.0u m=1 mimflag=3 \
        mismatchflag=0
C6 (OUTN net063 VDD) mimcap_um_sin_rf lt=20u wt=20u m=1 mimflag=3 \
        mismatchflag=0
C43 (IN_INT net011 VDD) mimcap_um_sin_rf lt=16.0u wt=16.0u m=1 mimflag=3 \
        mismatchflag=0
C5 (OUTP net033 VDD) mimcap_um_sin_rf lt=20u wt=20u m=1 mimflag=3 \
        mismatchflag=0
C11 (net059 VDD VDD) mimcap_um_sin_rf lt=100.0000u wt=50u m=1 mimflag=3 \
        mismatchflag=0
C8 (net047 VDD VDD) mimcap_um_sin_rf lt=100.0000u wt=50u m=1 mimflag=3 \
        mismatchflag=0
M10 (VDD net033 VOUTP VOUTP) nmos_rf lr=120.0n wr=2u nr=32 sigma=1 m=1 \
        mismatchflag=0
M12 (VDD net063 VOUTN VOUTN) nmos_rf lr=120.0n wr=2u nr=32 sigma=1 m=1 \
        mismatchflag=0
M4 (OUTN net011 VSS VSS) nmos_rf lr=60n wr=1u nr=10 sigma=1 m=4 \
        mismatchflag=0
M13 (OUTP net0252 IN_INT IN_INT) nmos_rf lr=60n wr=1u nr=10 sigma=1 m=1 \
        mismatchflag=0
R38 (net058 net057 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R0 (VOUTP VSS VDD) rppolys_rf l=20u w=1u m=1 mismatchflag=0
R36 (net042 net056 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R35 (net056 net055 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R34 (net055 net054 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R33 (net054 net060 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R41 (OUTN net032 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R32 (net060 OUTP VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R1 (VOUTN VSS VDD) rppolys_rf l=20u w=1u m=1 mismatchflag=0
R40 (net032 VDD VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R37 (net057 net042 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
R39 (VDD net058 VDD) rppolyl_rf l=24.0u w=3u m=1 mismatchflag=0
L8 (net047 OUTP VSS) spiral_std_mu_z w=3u rad=41.0u nr=3.75 lay=9 \
        spacing=2u gdis=10u m=1
L9 (net059 OUTN VSS) spiral_std_mu_z w=3u rad=39.0u nr=3.75 lay=9 \
        spacing=2u gdis=10u m=1
