.subckt powertrain_cell ond vcc vout
mmp0 vout ond vcc vcc p w=180n l=40n nfin=4 nf=8 m=4
.ends

.subckt powertrain_thermo on_d[15] on_d[14] on_d[13] on_d[12] on_d[11] on_d[10] on_d[9] on_d[8] on_d[7] on_d[6] on_d[5] on_d[4] on_d[3] on_d[2] on_d[1] on_d[0] vcc vout
xu_pmos_title[15] on_d[15] vcc vout powertrain_cell
xu_pmos_title[14] on_d[14] vcc vout powertrain_cell
xu_pmos_title[13] on_d[13] vcc vout powertrain_cell
xu_pmos_title[12] on_d[12] vcc vout powertrain_cell
xu_pmos_title[11] on_d[11] vcc vout powertrain_cell
xu_pmos_title[10] on_d[10] vcc vout powertrain_cell
xu_pmos_title[9] on_d[9] vcc vout powertrain_cell
xu_pmos_title[8] on_d[8] vcc vout powertrain_cell
xu_pmos_title[7] on_d[7] vcc vout powertrain_cell
xu_pmos_title[6] on_d[6] vcc vout powertrain_cell
xu_pmos_title[5] on_d[5] vcc vout powertrain_cell
xu_pmos_title[4] on_d[4] vcc vout powertrain_cell
xu_pmos_title[3] on_d[3] vcc vout powertrain_cell
xu_pmos_title[2] on_d[2] vcc vout powertrain_cell
xu_pmos_title[1] on_d[1] vcc vout powertrain_cell
xu_pmos_title[0] on_d[0] vcc vout powertrain_cell
.ends
