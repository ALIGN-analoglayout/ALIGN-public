.model resistor res r=1
.model capacitor cap c=1
.model inductor ind ind=1
.model n nmos nfin=1 w=1 nf=1 l=1 m=1 dd=0
.model p pmos nfin=1 w=1 nf=1 l=1 m=1 dd=0
.model phvt pmos l=1 w=1 nf=1 m=1
.model nhvt nmos l=1 w=1 nf=1 m=1
.model psvt pmos l=1 w=1 nf=1 m=1
.model nsvt nmos l=1 w=1 nf=1 m=1
.model plvt pmos l=1 w=1 nf=1 m=1
.model nlvt nmos l=1 w=1 nf=1 m=1
.model npv nmos nfin=1 w=1 nf=1 l=1 m=1 source=sig drain=sig
.model ppv pmos nfin=1 w=1 nf=1 l=1 m=1 source=sig drain=sig
