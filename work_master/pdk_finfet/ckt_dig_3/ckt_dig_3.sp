.subckt dig22inv a o vccx vssx
.ends
.subckt ckt_dig_3 vi vo vccx vssx
xi0 vi v1 vccx vssx dig22inv
xi1 v1 v2 vccx vssx dig22inv
xi2 v2 vo vccx vssx dig22inv
.ends ckt_dig_3
.END
