* Let PDK define the supported models. Do not require netlist to contain model statements.
.model n nmos nfin=2 nf=2 m=1
.model p pmos nfin=2 nf=2 m=1

.subckt ota_five_t vbias vcc vss von vin vip
    mn2 tail vbias vss vss n nfin=4 nf=2 m=8
    mn3 vop vip tail vss n nfin=4 nf=2 m=16
    mn4 von vin tail vss n nfin=4 nf=2 m=16
    mp5 vop vop vcc vcc p nfin=4 nf=2 m=4
    mp6 von vop vcc vcc p nfin=4 nf=2 m=4
.ends ota_five_t
