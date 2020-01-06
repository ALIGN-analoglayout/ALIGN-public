** Generated for: hspiceD
** Generated on: Jan  6 02:20:37 2020
** Design library name: GF_14nm_test1
** Design cell name: 2019_10_24_simple_SC_converter
** Design view name: schematic
.GLOBAL vdd!
.LIB "/project/design-kits/GF_PDKs/12nm/PDK/GF-12LP/12LP/V1.0_1.4/Models/HSPICE/models/12LP_Hspice.lib" TT
.PARAM wireopt=3
.OP
.TRAN 1e-9 5e-6
.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: GF_14nm_test1
** Cell name: 2019_10_24_simple_SC_converter
** View name: schematic
v3 vss 0 DC=0
v0 vin 0 DC=1
v2 phi2 0 PULSE 2 0 2.55e-9 25e-12 25e-12 2.4e-9 5e-9
v1 phi1 0 PULSE 2 0 50e-12 25e-12 25e-12 2.4e-9 5e-9
xc1 vout 0 apmom1v2 m=100 w=59.964e-6 l=60e-6 botlev=1 toplev=3 par=100
xc0 net1 0 apmom1v2 m=20 w=59.964e-6 l=60e-6 botlev=1 toplev=3 par=20
xp0 net1 phi2 vin vdd! pfet m=1 l=14e-9 nfin=40 nf=10 par=1 par_nf=10 asej=142.56e-15 adej=118.8e-15 psej=26.8e-6 pdej=21.6e-6 pdevdops=1 pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78e-9 fpitch=48e-9 xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 pre_layout_local=-1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71e-9 lle_sb=71e-9 lle_rxrxa=78e-9 lle_rxrxb=78e-9 lle_rxrxn=192e-9 lle_rxrxs=192e-9 lle_pcrxn=55e-9 lle_pcrxs=55e-9 lle_nwa=2e-6 lle_nwb=2e-6 lle_nwn=192e-9 lle_nws=192e-9 lle_ctne=0 lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 lrsd=27e-9 dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
xp1 vout phi1 net1 vdd! pfet m=1 l=14e-9 nfin=40 nf=10 par=1 par_nf=10 asej=142.56e-15 adej=118.8e-15 psej=26.8e-6 pdej=21.6e-6 pdevdops=1 pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78e-9 fpitch=48e-9 xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 pre_layout_local=-1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71e-9 lle_sb=71e-9 lle_rxrxa=78e-9 lle_rxrxb=78e-9 lle_rxrxn=192e-9 lle_rxrxs=192e-9 lle_pcrxn=55e-9 lle_pcrxs=55e-9 lle_nwa=2e-6 lle_nwb=2e-6 lle_nwn=192e-9 lle_nws=192e-9 lle_ctne=0 lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 lrsd=27e-9 dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
r0 vout 0 225
.MEAS TRAN avgcondv AVG V(vin) FROM=3e-6 TO=5e-6
.MEAS TRAN avgcondi AVG I(v0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_cond AVG par('-V(vin)*I(v0)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1v AVG V(phi1) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi1i AVG I(v1) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi1 AVG par('-V(phi1)*I(v1)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2v AVG V(phi2) FROM=3e-6 TO=5e-6
.MEAS TRAN avgphi2i AVG I(v2) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_phi2 AVG par('-V(phi2)*I(v2)') FROM=3e-6 TO=5e-6
.MEAS TRAN avgoutv AVG V(vout) FROM=3e-6 TO=5e-6
.MEAS TRAN avgouti AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS TRAN pow_out AVG par('V(vout)*I(r0)') FROM=3e-6 TO=5e-6
.MEAS efficiency PARAM='pow_out*100/(pow_cond+pow_phi1+pow_phi2)'
.MEAS output_power PARAM='pow_out'
.MEAS output_current AVG I(r0) FROM=3e-6 TO=5e-6
.MEAS output_voltage AVG V(vout) FROM=3e-6 TO=5e-6
.END

