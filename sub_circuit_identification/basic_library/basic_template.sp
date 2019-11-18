.subckt Switch_NMOS  D G S
M0 (D G S 0) NMOS w=w1 l=l1
.ends Switch_NMOS

.subckt Switch_PMOS  D G S
M0 (D G S 0) PMOS w=w1 l=l1
.ends Switch_PMOS

.subckt DCL_NMOS D S
M0 (D D S 0) NMOS w=w l=90n
.ends DCL_NMOS

.subckt DCL_PMOS D S
M0 (D D S 0) PMOS w=w l=90n
.ends DCL_PMOS
