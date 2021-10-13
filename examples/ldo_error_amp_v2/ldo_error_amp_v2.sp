.model phplvt pmos nfin=1 m=1
.model nhplvt nmos nfin=1 m=1

.SUBCKT pcell_0 b d g s
.param m=1
Mi1[0] n0 g s b phplvt nfin=6 m=1
Mi0[0] d g n0 b phplvt nfin=6 m=1
.ENDS

.SUBCKT pcell_1 d g s vssx
.param m=1
Mi1[0] d g n0 vssx nhplvt nfin=6 m=1
Mi0[0] n0 g s vssx nhplvt nfin=6 m=1
.ENDS

.SUBCKT ldo_error_amp_v2 vbias vcc vin vip vout vssx
Xi27 vcc n2 n2 vcc pcell_0 m=8
Xi26 vcc n1 n1 vcc pcell_0 m=8
Xi33 vcc vout n1 vcc pcell_0 m=16
Xi41 vcc n4 n2 vcc pcell_0 m=16
Xi29 n1 vip vcom vssx pcell_1 m=16
Xi28 n2 vin vcom vssx pcell_1 m=16
Xi43 n4 n4 vssx vssx pcell_1 m=16
Xi34 vout n4 vssx vssx pcell_1 m=16
Xi30 vcom vbias vssx vssx pcell_1 m=16
Xi31 vbias vssx vssx vssx pcell_1 m=4
.ENDS
