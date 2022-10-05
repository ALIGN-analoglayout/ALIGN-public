.subckt dig22inv a o vccx vssx
.ends
.subckt dig22nand a b o vccx vssx
.ends
.subckt ckt_dig_5_tamu_sp p n nob vccx vssx
xi0 p en pob vccx vssx dig22nand
xi1 en p nob vccx vssx dig22nand
xi2 nob nob vccx vssx dig22inv
mn1 vssx pob vssx vssx n w=360e-9 m=1 nf=4
mn2 vssx nob vssx vssx n w=360e-9 m=1 nf=4
.ends ckt_dig_5_tamu_sp
.END
