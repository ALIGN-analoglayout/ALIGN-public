// Generated for: spectre
// Generated on: Jan  5 09:35:33 2020
// Design library name: EQ_01032020
// Design cell name: CTLE_top
// Design view name: schematic
simulator lang=spectre
global 0 vdd!
//include "$SPECTRE_MODEL_PATH/12LP_Spectre.lib" section=tt
include "/project/design-kits/GF_PDKs/12nm/PDK/GF-12LP/12LP/V1.0_1.4/Models/Spectre/models/12LP_Spectre.lib" section=tt
parameters vs3=0.85 vs4=0 vs5=0 vs2=0.85 vs1=0.85 nfpf_ctle_sw0=40 ngf_ctle_sw0=1 \
    vs0=0.85 Cs=25f Rs=100 cload=10f ib_ctle=180u nfpf_ctle_cm=80 \
    nfpf_ctle_dp=50 ngf_ctle_cm=1 ngf_ctle_dp=1 rload_ctle=800 vbias=594m \
    vps=0.85 wireopt=9

// Library name: EQ_01032020
// Cell name: CTLE_top
// View name: schematic
V6 (s3_ctle 0) vsource dc=vs3 type=dc
V5 (s2_ctle 0) vsource dc=vs2 type=dc
V4 (s1_ctle 0) vsource dc=vs1 type=dc
V3 (s0_ctle 0) vsource dc=vs0 type=dc
V1 (vdd! 0) vsource dc=vps type=dc
V0 (vcm_ctle 0) vsource dc=vbias type=dc
C2 (vout2_ctle 0) capacitor c=cload
C1 (vout1_ctle 0) capacitor c=cload
V2 (vac 0) vsource dc=0 mag=2 type=sine ampl=200m freq=1G
I25 (vdd! net048) isource dc=ib_ctle type=dc
E2 (vin2 vcm_ctle vac 0) vcvs gain=-0.5
E0 (vin1 vcm_ctle vac 0) vcvs gain=0.5
N33 (net066 vin2 net055 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N32 (vout2_ctle vin2 net066 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N31 (net055 net048 net065 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) \
        par_nf=(1)*(7) asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 \
        pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 \
        plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 \
        scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
N30 (net065 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) par_nf=(1)*(7) \
        asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 \
        psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdevdops=1 pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 \
        pldist=1 plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 \
        sca=0 scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
N29 (net074 s2_ctle net068 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N28 (net073 s1_ctle net067 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N27 (net072 s3_ctle net070 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N26 (net071 s0_ctle net069 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N25 (net075 s0_ctle net071 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N24 (net076 s3_ctle net072 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N23 (net077 s1_ctle net073 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N20 (net078 s2_ctle net074 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N19 (net079 vin1 net052 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N18 (net080 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) par_nf=(1)*(7) \
        asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 \
        psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdevdops=1 pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 \
        pldist=1 plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 \
        sca=0 scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
N17 (net052 net048 net080 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) \
        par_nf=(1)*(7) asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 \
        pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 \
        plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 \
        scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
N16 (vout1_ctle vin1 net079 0) nfet m=1 l=14n nfin=12 nf=4 par=(1) \
        par_nf=(1)*(4) asej=((54n)+(54n))*(11n)*12 + 12*1*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=12*2*(((78n)-(14n)-(10n)-(0))*(11n)) psej=(1)*12*((54n)*2+(11n)+(54n)*2+(11n)) + 12*1*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=12*2*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 pdevlgeos=1 \
        pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 plorient=0 cpp=78n \
        fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 scb=0 scc=0 \
        pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 u0mult_fet=1 lle_sa=71n \
        lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n lle_rxrxn=192n \
        lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n lle_nwa=2u lle_nwb=2u \
        lle_nwn=192n lle_nws=192n lle_ctne=0 lle_ctnw=0 lle_ctse=0 \
        lle_ctsw=0 lle_sctne=0 lle_sctnw=0 lle_sctse=0 lle_sctsw=0 \
        lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 nsig_dop1=0 nsig_dop2=0 \
        nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 fc_sigma=3
N22 (net081 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) par_nf=(1)*(7) \
        asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 \
        psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdevdops=1 pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 \
        pldist=1 plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 \
        sca=0 scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
N21 (net048 net048 net081 0) nfet m=1 l=14n nfin=12 nf=7 par=(1) \
        par_nf=(1)*(7) asej=(54n)*(11n)*12 + 12*3*(((78n)-(14n)-(10n)-(0))*(11n)) \
         adej=(54n)*(11n)*12+3*(((78n)-(14n)-(10n)-(0))*(11n))*12 psej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) \
         pdej=(1)*12*(2*(54n)+(11n)) + 12*3*(1)*2*((78n)-(14n)-(10n)-(0)) pdevdops=1 \
        pdevlgeos=1 pdevwgeos=1 psw_acv_sign=1 plnest=1 pldist=1 \
        plorient=0 cpp=78n fpitch=48n xpos=-99 ypos=-99 ptwell=0 sca=0 \
        scb=0 scc=0 pre_layout_local=1 ngcon=1 p_vta=0 p_la=0 \
        u0mult_fet=1 lle_sa=71n lle_sb=71n lle_rxrxa=78n lle_rxrxb=78n \
        lle_rxrxn=192n lle_rxrxs=192n lle_pcrxn=55n lle_pcrxs=55n \
        lle_nwa=2u lle_nwb=2u lle_nwn=192n lle_nws=192n lle_ctne=0 \
        lle_ctnw=0 lle_ctse=0 lle_ctsw=0 lle_sctne=0 lle_sctnw=0 \
        lle_sctse=0 lle_sctsw=0 lrsd=27n dtemp=0 l_shape=0 l_shape_s=0 \
        nsig_dop1=0 nsig_dop2=0 nsig_dibl=0 nsig_pc=0 nsig_rx=0 fc_index=0 \
        fc_sigma=3
R13 (net069 net055) metalres w=32n l=40.144u metLayer=15
R12 (net070 net055) metalres w=32n l=40.144u metLayer=15
R11 (vout2_ctle vdd!) metalres w=32n l=73.626u metLayer=15
R10 (net052 net075) metalres w=32n l=40.144u metLayer=15
R9 (net052 net076) metalres w=32n l=40.144u metLayer=15
R2 (vout1_ctle vdd!) metalres w=32n l=73.626u metLayer=15
C11 (net055 net068) apmom1v2 m=1 w=5.724u l=3.2u botlev=1 toplev=3 par=(1)
C10 (net055 net067) apmom1v2 m=1 w=5.724u l=3.2u botlev=1 toplev=3 par=(1)
C9 (net052 net077) apmom1v2 m=1 w=5.724u l=3.2u botlev=1 toplev=3 par=(1)
C0 (net052 net078) apmom1v2 m=1 w=5.724u l=3.2u botlev=1 toplev=3 par=(1)
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
tran tran stop=10n errpreset=conservative write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
ac ac start=10000 stop=100G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
