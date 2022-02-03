.subckt INV i zn SN SP
M0 zn i SN SN NMOS w=w0 l=l0
M1 zn i SP SP PMOS w=w1 l=l0
.ends INV

.subckt INV_B i zn SN SP PB
M0 zn i SN SN NMOS w=w0 l=l0
M1 zn i SP PB PMOS w=w1 l=l0
.ends INV_B

.subckt tgate GA GB D S BN BP
M0 D GA S BN NMOS w=w l=90n
M1 D GB S BP PMOS w=w l=90n
.ends tgate
