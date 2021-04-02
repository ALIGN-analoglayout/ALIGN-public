* Let PDK define the supported models. Do not require netlist to contain model statements.
.model n nmos nfin=2 nf=2 m=1
.model p pmos nfin=2 nf=2 m=1

.subckt ring_oscillator_stage vi vo vss vcc vctl
mp0 vo vi vctl vcc p nfin=4 l=40n m=2
mn0 vo vi vss  vss n nfin=4 l=40n m=2
.ends ring_oscillator_stage

.subckt ring_oscillator vctl vo vcc vss
xi0 vo n1 vss vcc vctl ring_oscillator_stage
xi1 n1 n2 vss vcc vctl ring_oscillator_stage
xi2 n2 n3 vss vcc vctl ring_oscillator_stage
xi3 n3 n4 vss vcc vctl ring_oscillator_stage
xi4 n4 vo vss vcc vctl ring_oscillator_stage
.ends ring_oscillator