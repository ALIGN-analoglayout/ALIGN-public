* .subckt Switch_NMOS_B  D G S B
* M0 D G S B NMOS w=w1 l=l1
* .ends Switch_NMOS_B

* .subckt Switch_PMOS_B D G S B
* M0 D G S B PMOS w=w1 l=l1
* .ends Switch_PMOS_B

* .subckt Switch_NMOS  D G S
* M0 D G S S NMOS w=w1 l=l1
* .ends Switch_NMOS

* .subckt Switch_PMOS D G S
* M0 D G S S PMOS w=w1 l=l1
* .ends Switch_PMOS

* .subckt Switch_NMOS_G  D G S
* M0 D G S G NMOS w=w1 l=l1
* .ends Switch_NMOS_G

* .subckt Switch_PMOS_G D G S
* M0 D G S G PMOS w=w1 l=l1
* .ends Switch_PMOS_G

.subckt SCM_NMOS_B DA DB S B
M0 DA DA S B NMOS w=w l=90n
M1 DB DA S B NMOS w=w l=90n
.ends SCM_NMOS_B

.subckt SCM_PMOS_B DA DB S B
M0 DA DA S B PMOS w=w l=90n
M1 DB DA S B PMOS w=w l=90n
.ends SCM_PMOS_B

.subckt SCM_NMOS DA DB S
M0 DA DA S S NMOS w=w l=90n
M1 DB DA S S NMOS w=w l=90n
.ends SCM_NMOS

.subckt SCM_PMOS DA DB S
M0 DA DA S S PMOS w=w l=90n
M1 DB DA S S PMOS w=w l=90n
.ends SCM_PMOS

.subckt CMC_S_NMOS_B DA DB SA SB G B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA G SA B NMOS w=w l=90n
M1 DB G SB B NMOS w=w l=90n
.ends CMC_S_NMOS_B

.subckt CMC_S_NMOS DA DB SA SB G
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA G SA SB NMOS w=w l=90n
M1 DB G SB SB NMOS w=w l=90n
.ends CMC_S_NMOS

.subckt CMC_S_PMOS_B DA DB SA SB G B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA G SA B PMOS w=w l=90n
M1 DB G SB B PMOS w=w l=90n
.ends CMC_S_PMOS_B

.subckt CMC_NMOS  DA DB G S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA G S S NMOS w=w l=90n
M1 DB G S S NMOS w=w l=90n
.ends CMC_NMOS

.subckt CMC_PMOS  DA DB G S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA G S S PMOS w=w l=90n
M1 DB G S S PMOS w=w l=90n
.ends CMC_PMOS

.subckt CMC_NMOS_B  DA DB G S B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA G S B NMOS w=w l=90n
M1 DB G S B NMOS w=w l=90n
.ends CMC_NMOS_B

.subckt CMC_S_PMOS  DA DB G S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA G SA SA PMOS w=w l=90n
M1 DB G SB SB PMOS w=w l=90n
.ends CMC_S_PMOS

.subckt DP_NMOS_B  DA DB GA GB S B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA GA S B NMOS w=w l=90n
M1 DB GB S B NMOS w=w l=90n
.ends DP_NMOS_B

.subckt DP_PMOS_B  DA DB GA GB S B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA GA S B PMOS w=w l=90n
M1 DB GB S B PMOS w=w l=90n
.ends DP_PMOS_B

.subckt DP_NMOS  DA DB GA GB S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA GA S S NMOS w=w l=90n
M1 DB GB S S NMOS w=w l=90n
.ends DP_NMOS

.subckt DP_PMOS  DA DB GA GB S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA GA S S PMOS w=w l=90n
M1 DB GB S S PMOS w=w l=90n
.ends DP_PMOS

.subckt CCP_S_NMOS_B DA DB SA SB B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA DB SA B NMOS w=w l=90n
M1 DB DA SB B NMOS w=w l=90n
.ends CCP_NMOS_B

.subckt CCP_S_PMOS_B DA DB SA SB B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA DB SA B PMOS w=w l=90n
M1 DB DA SB B PMOS w=w l=90n
.ends CCP_PMOS_B

.subckt CCP_NMOS DA DB S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA DB S S NMOS w=w l=90n
M1 DB DA S S NMOS w=w l=90n
.ends CCP_NMOS

.subckt CCP_PMOS DA DB S
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA DB S S PMOS w=w l=90n
M1 DB DA S S PMOS w=w l=90n
.ends CCP_PMOS

.subckt CCP_NMOS_B DA DB S B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA DB S B NMOS w=w l=90n
M1 DB DA S B NMOS w=w l=90n
.ends CCP_NMOS_B

.subckt CCP_PMOS_B DA DB S B
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='S',net2='S',  direction='V')
M0 DA DB S B PMOS w=w l=90n
M1 DB DA S B PMOS w=w l=90n
.ends CCP_PMOS_B

.subckt LS_S_NMOS_B DA DB SA SB
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA DA SA B NMOS w=w l=90n
M1 DB DA SB B NMOS w=w l=90n
.ends LS_NMOS_B

.subckt LS_S_PMOS_B DA DB SA SB
* @: SymmetricBlocks(pairs=[['M0','M1']], direction='V')
* @: SymmetricNets(net1='DA',net2='DB',  direction='V')
* @: SymmetricNets(net1='SA',net2='SB',  direction='V')
M0 DA DA SA B PMOS w=w l=90n
M1 DB DA SB B PMOS w=w l=90n
.ends LS_S_PMOS_B

* .subckt DCL_NMOS_B D S B
* M0 D D S B NMOS w=w l=90n
* .ends DCL_NMOS_B

* .subckt DCL_PMOS_B D S B
* M0 D D S B PMOS w=w l=90n
* .ends DCL_PMOS_B

* .subckt DCL_NMOS D S
* M0 D D S S NMOS w=w l=90n
* .ends DCL_NMOS

* .subckt DCL_PMOS D S
* M0 D D S S PMOS w=w l=90n
* .ends DCL_PMOS

* .subckt Dummy_NMOS_B D S B
* M0 D S S B NMOS w=w l=90n
* .ends Dummy_NMOS_B

* .subckt Dummy_PMOS_B D S B
* M0 D S S B PMOS w=w l=90n
* .ends Dummy_PMOS_B

* .subckt Dummy_NMOS D S
* M0 D S S S NMOS w=w l=90n
* .ends Dummy_NMOS

* .subckt Dummy_PMOS D S
* M0 D S S S PMOS w=w l=90n
* .ends Dummy_PMOS

* .subckt Dcap_NMOS_B G S B
* M0 S G S B NMOS w=w l=90n
* .ends Dcap_NMOS_B

* .subckt Dcap_PMOS_B G S B
* M0 S G S B PMOS w=w l=90n
* .ends Dcap_PMOS_B

* .subckt Dcap_NMOS G S
* M0 S G S S NMOS w=w l=90n
* .ends Dcap_NMOS

* .subckt Dcap_PMOS G S
* M0 S G S S PMOS w=w l=90n
* .ends Dcap_PMOS

* .subckt Dummy1_NMOS_B S B
* M0 S S S B NMOS w=w l=90n
* .ends Dummy1_NMOS_B

* .subckt Dummy1_PMOS_B S B
* M0 S S S B PMOS w=w l=90n
* .ends Dummy1_PMOS_B

* .subckt Dummy1_NMOS S
* M0 (S S S S) NMOS w=w l=90n
* .ends Dummy1_NMOS

* .subckt Dummy1_PMOS S
* M0 (S S S S) PMOS w=w l=90n
* .ends Dummy1_PMOS

* .subckt Res PLUS MINUS
* RR1 PLUS MINUS res res=10k
* .ends Res

* .subckt Cap_b PLUS MINUS BULK
* CC1 PLUS MINUS BULK cap cap=60f
* .ends Cap_b

* .subckt Cap PLUS MINUS
* CC1 PLUS MINUS cap cap=60f
* .ends Cap
