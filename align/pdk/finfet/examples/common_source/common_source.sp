* Let PDK define the supported models. Do not require netlist to contain model statements.
.model n nmos nfin=2 nf=2 m=1
.model p pmos nfin=2 nf=2 m=1

.subckt common_source vin vop vcc vss
mp0 vop vop vcc vcc p nfin=4 nf=4 m=4
mn0 vop vin vss vss n nfin=4 nf=4 m=4
.ends common_source
