.subckt NMOS_4T  D G S B
* @: Generator(name='mos')
M1 D G S B NMOS
.ends NMOS_4T

.subckt PMOS_4T  D G S B
* @: Generator(name='mos')
M1 D G S B PMOS
.ends PMOS_4T

.subckt TFR  A B
* @: Generator()
XR1 A B TFR
.ends TFR

.subckt NMOS_S  D G S
* @: Generator(name='mos')
M1 D G S S NMOS w=w1 l=l1
.ends NMOS_S

.subckt PMOS_S D G S
* @: Generator(name='mos')
M1 D G S S PMOS w=w1 l=l1
.ends PMOS_S

.subckt NMOS_G  D G S
* @: Generator(name='mos')
M1 D G S G NMOS w=w1 l=l1
.ends NMOS_G

.subckt PMOS_G D G S
* @: Generator(name='mos')
M1 D G S G PMOS w=w1 l=l1
.ends PMOS_G

.subckt DUMMY_NMOS_S D S
* @: Generator(name='mos')
M1 D S S S NMOS w=w l=90n
.ends DUMMY_NMOS_S

.subckt DUMMY_PMOS_S D S
* @: Generator(name='mos')
M1 D S S S PMOS w=w l=90n
.ends DUMMY_PMOS_S

.subckt DCAP_NMOS_B G S B
* @: Generator(name='mos')
M1 S G S B NMOS w=w l=90n
.ends DCAP_NMOS_B

.subckt DCAP_PMOS_B G S B
* @: Generator(name='mos')
M1 S G S B PMOS w=w l=90n
.ends DCAP_PMOS_B

.subckt DCAP_NMOS G S
* @: Generator(name='mos')
M1 S G S S NMOS w=w l=90n
.ends DCAP_NMOS

.subckt DCAP_PMOS G S
* @: Generator(name='mos')
M1 S G S S PMOS w=w l=90n
.ends DCAP_PMOS

.subckt DCL_NMOS D S B
* @: Generator(name='mos')
M1 D D S B NMOS w=w l=90n
.ends DCL_NMOS

.subckt DCL_PMOS D S B
* @: Generator(name='mos')
M1 D D S B PMOS w=w l=90n
.ends DCL_PMOS

.subckt DCL_NMOS_S D S
* @: Generator(name='mos')
M1 D D S S NMOS w=w l=90n
.ends DCL_NMOS_S

.subckt DCL_PMOS_S D S
* @: Generator(name='mos')
M1 D D S S PMOS w=w l=90n
.ends DCL_PMOS_S

.subckt DUMMY_NMOS D S B
* @: Generator(name='mos')
M1 D S S B NMOS w=w l=90n
.ends DUMMY_NMOS

.subckt DUMMY_PMOS D S B
* @: Generator(name='mos')
M1 D S S B PMOS w=w l=90n
.ends DUMMY_PMOS

.subckt DUMMY1_NMOS S B
* @: Generator(name='mos')
M1 S S S B NMOS w=w l=90n
.ends DUMMY1_NMOS

.subckt DUMMY1_PMOS S B
* @: Generator(name='mos')
M1 S S S B PMOS w=w l=90n
.ends DUMMY1_PMOS

.subckt DUMMY1_NMOS_S S
* @: Generator(name='mos')
M1 S S S S NMOS w=w l=90n
.ends DUMMY1_NMOS_S

.subckt DUMMY1_PMOS_S S
* @: Generator(name='mos')
M1 S S S S PMOS w=w l=90n
.ends DUMMY1_PMOS_S

.subckt SCM_NMOS_B DA DB S B
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
M1 DA DA S B NMOS w=w l=90n
M2 DB DA S B NMOS w=w l=90n
.ends SCM_NMOS_B

.subckt SCM_PMOS_B DA DB S B
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
M1 DA DA S B PMOS w=w l=90n
M2 DB DA S B PMOS w=w l=90n
.ends SCM_PMOS_B

.subckt SCM_NMOS DA DB S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
M1 DA DA S S NMOS w=w l=90n
M2 DB DA S S NMOS w=w l=90n
.ends SCM_NMOS

.subckt SCM_PMOS DA DB S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
M1 DA DA S S PMOS w=w l=90n
M2 DB DA S S PMOS w=w l=90n
.ends SCM_PMOS

.subckt CMC_S_NMOS_B DA DB SA SB G B
* @: Generator(name='mos', parameters={'pattern':'ncc' , 'parallel_wires':{'DA':1, 'DB':1}})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA G SA B NMOS w=w l=90n
M2 DB G SB B NMOS w=w l=90n
.ends CMC_S_NMOS_B

.subckt CMC_S_NMOS DA DB SA SB G
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA G SA SA NMOS w=w l=90n
M2 DB G SB SB NMOS w=w l=90n
.ends CMC_S_NMOS

.subckt CMC_S_PMOS_B DA DB SA SB G B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA G SA B PMOS w=w l=90n
M2 DB G SB B PMOS w=w l=90n
.ends CMC_S_PMOS_B

.subckt CMC_NMOS  DA DB G S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA G S S NMOS w=w l=90n
M2 DB G S S NMOS w=w l=90n
.ends CMC_NMOS

.subckt CMC_PMOS  DA DB G S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA G S S PMOS w=w l=90n
M2 DB G S S PMOS w=w l=90n
.ends CMC_PMOS

.subckt CMC_NMOS_B  DA DB G S B
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA G S B NMOS w=w l=90n
M2 DB G S B NMOS w=w l=90n
.ends CMC_NMOS_B

.subckt CMC_S_PMOS  DA DB G SA SB
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA G SA SA PMOS w=w l=90n
M2 DB G SB SB PMOS w=w l=90n
.ends CMC_S_PMOS

.subckt DP_NMOS_B  DA DB GA GB S B
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA GA S B NMOS w=w l=90n
M2 DB GB S B NMOS w=w l=90n
.ends DP_NMOS_B

.subckt DP_PMOS_B  DA DB GA GB S B
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA GA S B PMOS w=w l=90n
M2 DB GB S B PMOS w=w l=90n
.ends DP_PMOS_B

.subckt DP_NMOS  DA DB GA GB S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA GA S S NMOS w=w l=90n
M2 DB GB S S NMOS w=w l=90n
.ends DP_NMOS

.subckt DP_PMOS  DA DB GA GB S
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA GA S S PMOS w=w l=90n
M2 DB GB S S PMOS w=w l=90n
.ends DP_PMOS

.subckt CCP_S_NMOS_B DA DB SA SB B
* @: Generator(name='mos',parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA DB SA B NMOS w=w l=90n
M2 DB DA SB B NMOS w=w l=90n
.ends CCP_NMOS_B

.subckt CCP_S_PMOS_B DA DB SA SB B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA DB SA B PMOS w=w l=90n
M2 DB DA SB B PMOS w=w l=90n
.ends CCP_PMOS_B

.subckt CCP_NMOS DA DB S
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA DB S S NMOS w=w l=90n
M2 DB DA S S NMOS w=w l=90n
.ends CCP_NMOS

.subckt CCP_PMOS DA DB S
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA DB S S PMOS w=w l=90n
M2 DB DA S S PMOS w=w l=90n
.ends CCP_PMOS

.subckt CCP_NMOS_B DA DB S B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA DB S B NMOS w=w l=90n
M2 DB DA S B NMOS w=w l=90n
.ends CCP_NMOS_B

.subckt CCP_PMOS_B DA DB S B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M1 DA DB S B PMOS w=w l=90n
M2 DB DA S B PMOS w=w l=90n
.ends CCP_PMOS_B

.subckt LS_S_NMOS_B DA DB SA SB B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA DA SA B NMOS w=w l=90n
M2 DB DA SB B NMOS w=w l=90n
.ends LS_NMOS_B

.subckt LS_S_PMOS_B DA DB SA SB B
* @: Generator(name='mos', parameters={'pattern':'ncc'})
* @: SymmetricBlocks(pairs=[['M1','M2']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M1 DA DA SA B PMOS w=w l=90n
M2 DB DA SB B PMOS w=w l=90n
.ends LS_S_PMOS_B
