.subckt tfr a b
* @: Generator()
xr1 a b tfr
.ends tfr

.subckt nmos_3t d g s
* @: Generator(name='mos')
m1 d g s s nmos w=w1 l=l1
.ends nmos_3t

.subckt pmos_3t d g s
* @: Generator(name='mos')
m1 d g s s pmos w=w1 l=l1
.ends pmos_3t

.subckt nmos_4t d g s b
* @: Generator(name='mos')
m1 d g s b nmos
.ends nmos_4t

.subckt pmos_4t d g s b
* @: Generator(name='mos')
m1 d g s b pmos
.ends pmos_4t

.subckt nmos_gb d g s
* @: Generator(name='mos')
m1 d g s g nmos w=w1 l=l1
.ends nmos_gb

.subckt pmos_gb d g s
* @: Generator(name='mos')
m1 d g s g pmos w=w1 l=l1
.ends pmos_gb

.subckt dcap_nmos_3t g s b
* @: Generator(name='mos')
m1 s g s b nmos w=w1 l=l1
.ends dcap_nmos_3t

.subckt dcap_pmos_3t g s b
* @: Generator(name='mos')
m1 s g s b pmos w=w1 l=l1
.ends dcap_pmos_3t

.subckt dcap_nmos g s
* @: Generator(name='mos')
m1 s g s s nmos w=w1 l=l1
.ends dcap_nmos

.subckt dcap_pmos g s
* @: Generator(name='mos')
m1 s g s s pmos w=w1 l=l1
.ends dcap_pmos

.subckt dcl_nmos_3t d s b
* @: Generator(name='mos')
m1 d d s b nmos w=w1 l=l1
.ends dcl_nmos_3t

.subckt dcl_pmos_3t d s b
* @: Generator(name='mos')
m1 d d s b pmos w=w1 l=l1
.ends dcl_pmos_3t

.subckt dcl_nmos_2t d s
* @: Generator(name='mos')
m1 d d s s nmos w=w1 l=l1
.ends dcl_nmos_2t

.subckt dcl_pmos_2t d s
* @: Generator(name='mos')
m1 d d s s pmos w=w1 l=l1
.ends dcl_pmos_2t

.subckt dummy_nmos_2t d s
* @: Generator(name='mos')
m1 d s s s nmos w=w1 l=l1
.ends dummy_nmos_2t

.subckt dummy_pmos_2t d s
* @: Generator(name='mos')
m1 d s s s pmos w=w1 l=l1
.ends dummy_pmos_2t

.subckt dummy_nmos_3t d s b
* @: Generator(name='mos')
m1 d s s b nmos w=w1 l=l1
.ends dummy_nmos_3t

.subckt dummy_pmos_3t d s b
* @: Generator(name='mos')
m1 d s s b pmos w=w1 l=l1
.ends dummy_pmos_3t

.subckt dummy_full_nmos s
* @: Generator(name='mos')
m1 s s s s nmos w=w1 l=l1
.ends dummy_full_nmos

.subckt dummy_full_pmos s
* @: Generator(name='mos')
m1 s s s s pmos w=w1 l=l1
.ends dummy_full_pmos

.subckt dummy_full_nmos_2t s b
* @: Generator(name='mos')
m1 s s s b nmos w=w1 l=l1
.ends dummy_full_nmos_2t

.subckt dummy_full_pmos_2t s b
* @: Generator(name='mos')
m1 s s s b pmos w=w1 l=l1
.ends dummy_full_pmos_2t

.subckt scm_nmos_b da db s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da s b nmos w=w1 l=l1
m2 db da s b nmos w=w1 l=l1
.ends scm_nmos_b

.subckt scm_pmos_b da db s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da s b pmos w=w1 l=l1
m2 db da s b pmos w=w1 l=l1
.ends scm_pmos_b

.subckt scm_nmos da db s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da s s nmos w=w1 l=l1
m2 db da s s nmos w=w1 l=l1
.ends scm_nmos

.subckt scm_pmos da db s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da s s pmos w=w1 l=l1
m2 db da s s pmos w=w1 l=l1
.ends scm_pmos

.subckt cmc_s_nmos_b da db sa sb g b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g sa b nmos w=w1 l=l1
m2 db g sb b nmos w=w1 l=l1
.ends cmc_s_nmos_b

.subckt cmc_s_nmos da db sa sb g
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g sa sa nmos w=w1 l=l1
m2 db g sb sb nmos w=w1 l=l1
.ends cmc_s_nmos

.subckt cmc_s_pmos_b da db sa sb g b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g sa b pmos w=w1 l=l1
m2 db g sb b pmos w=w1 l=l1
.ends cmc_s_pmos_b

.subckt cmc_nmos  da db g s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g s s nmos w=w1 l=l1
m2 db g s s nmos w=w1 l=l1
.ends cmc_nmos

.subckt cmc_pmos  da db g s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g s s pmos w=w1 l=l1
m2 db g s s pmos w=w1 l=l1
.ends cmc_pmos

.subckt cmc_nmos_b  da db g s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g s b nmos w=w1 l=l1
m2 db g s b nmos w=w1 l=l1
.ends cmc_nmos_b

.subckt cmc_s_pmos  da db g sa sb
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da g sa sa pmos w=w1 l=l1
m2 db g sb sb pmos w=w1 l=l1
.ends cmc_s_pmos

.subckt dp_nmos_b  da db ga gb s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da ga s b nmos w=w1 l=l1
m2 db gb s b nmos w=w1 l=l1
.ends dp_nmos_b

.subckt dp_pmos_b  da db ga gb s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da ga s b pmos w=w1 l=l1
m2 db gb s b pmos w=w1 l=l1
.ends dp_pmos_b

.subckt dp_nmos  da db ga gb s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da ga s s nmos w=w1 l=l1
m2 db gb s s nmos w=w1 l=l1
.ends dp_nmos

.subckt dp_pmos  da db ga gb s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da ga s s pmos w=w1 l=l1
m2 db gb s s pmos w=w1 l=l1
.ends dp_pmos

.subckt ccp_s_nmos_b da db sa sb b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db sa b nmos w=w1 l=l1
m2 db da sb b nmos w=w1 l=l1
.ends ccp_nmos_b

.subckt ccp_s_pmos_b da db sa sb b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db sa b pmos w=w1 l=l1
m2 db da sb b pmos w=w1 l=l1
.ends ccp_pmos_b

.subckt ccp_nmos da db s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db s s nmos w=w1 l=l1
m2 db da s s nmos w=w1 l=l1
.ends ccp_nmos

.subckt ccp_pmos da db s
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db s s pmos w=w1 l=l1
m2 db da s s pmos w=w1 l=l1
.ends ccp_pmos

.subckt ccp_nmos_b da db s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db s b nmos w=w1 l=l1
m2 db da s b nmos w=w1 l=l1
.ends ccp_nmos_b

.subckt ccp_pmos_b da db s b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da db s b pmos w=w1 l=l1
m2 db da s b pmos w=w1 l=l1
.ends ccp_pmos_b

.subckt ls_s_nmos_b da db sa sb b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da sa b nmos w=w1 l=l1
m2 db da sb b nmos w=w1 l=l1
.ends ls_nmos_b

.subckt ls_s_pmos_b da db sa sb b
* @: Generator(name='mos')
* @: SymmetricBlocks(pairs=[['m1','m2']], direction='V')
m1 da da sa b pmos w=w1 l=l1
m2 db da sb b pmos w=w1 l=l1
.ends ls_s_pmos_b
