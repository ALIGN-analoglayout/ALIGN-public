parameters fck1=1 fck2=2 finnn=2 fninv=4 fpinv=4 fprst=4 fttt=4 fout1=1 fout2=2 frdynand=2 fckbuf1_seq=2 frstbuf1_compckgen=1 fpinn_latch_M=4 fpinn_latch_L=2 bit_M_Latch=2 bit_L_Latch=4 
parameters fs=1G vos=100u VCM=400m VDD=0.8

.subckt INVERTER_1 A VDD VSS Z
parameters _par0 _par1
    m0 Z A VSS VSS nmos_rvt m=1 l=14n nfin=4 nf=_par0
    m1 Z A VDD VDD pmos_rvt m=1 l=14n nfin=6 nf=_par1
.ends INVERTER_1

.subckt INVERTER_2 A VDD VSS Z
parameters _par0 _par1
    m0 Z A VSS VSS nmos_rvt m=1 l=14n nfin=4 nf=_par0
    m1 Z A VDD VDD pmos_rvt m=1 l=14n nfin=6 nf=_par1
.ends INVERTER_2
// End of subcircuit definition.

.subckt NAND_1 A B Z VDD VSS
parameters fingern fppp
    m1 Z A net47 VSS nmos_rvt m=1 l=14n nfin=4 nf=fingern
    m3 net47 B VSS VSS nmos_rvt m=1 l=14n nfin=4 nf=fingern
    m4 Z B VDD VDD pmos_rvt m=1 l=14n nfin=6 nf=fppp
.ends NAND_1

.subckt NAND A B VDD VSS Z
parameters fingern fppp
I0 A B Z VDD VSS NAND_1 fingern=fingern fppp=fppp
I1 B A Z VDD VSS NAND_1 fingern=fingern fppp=fppp
.ends NAND

.subckt comparator AN AP BN BP CKi ON OP RDY VDD VSS oCK
parameters _par0 _par1 _par2 _par3 _par4 _par5 _par6 _par7
    m0 OP ON net65 VSS nmos_rvt m=1 l=14n nfin=4 nf=_par0
    m1 ON OP net61 VSS nmos_rvt m=1 l=14n nfin=4 nf=_par0
    m2 net65 BN net67 VSS nmos_rvt m=1 l=14n nfin=4 nf=_par1 
    m3 net67 oCK VSS VSS nmos_rvt m=1 l=14n nfin=4 nf= _par2
    m4 net61 BP net67 VSS nmos_rvt m=1 l=14n nfin=4 nf= _par1
    m5 net65 AN net60 VSS nmos_rvt m=1 l=14n nfin=4 nf= _par1
    m6 net60 oCK VSS VSS nmos_rvt m=1 l=14n nfin=4 nf= _par2
    m7 net61 AP net60 VSS nmos_rvt m=1 l=14n nfin=4 nf= _par1
    m8 OP oCK VDD VDD pmos_rvt m=1 l=14n nfin=6 nf= _par3
    m9 ON oCK VDD VDD pmos_rvt m=1 l=14n nfin=6 nf= _par3
    m10 OP ON VDD VDD pmos_rvt m=1 l=14n nfin=6 nf= _par4
    m11 ON OP VDD VDD pmos_rvt m=1 l=14n nfin=6 nf= _par4
    I5 CKi VDD VSS net019 INVERTER_1 _par0=_par5 _par1=_par5
    I4 net019 VDD VSS oCK INVERTER_2 _par0=_par6 _par1=_par6
    I2 OP ON VDD VSS RDY NAND fingern=_par7 fppp=_par7
.ends comparator
// End of subcircuit definition.

.subckt comparator1 AN AP BN BP CKi ON OP RDY VDD VSS oCK
I1 AN AP BN BP CKi ON OP RDY VDD VSS oCK comparator _par0=fninv _par1=finnn _par2=fttt _par3=fprst \
        _par4=fpinv _par5=fck1 _par6=fck2 _par7=frdynand
.ends comparator1
