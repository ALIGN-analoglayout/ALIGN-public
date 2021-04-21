.subckt mom_capacitor a b lowershield uppershield
xi0 a b lowershield uppershield b88xmfc_s2s_ds0w_varprim mtop=5 mbot=3 multx=1 multy=1
.ends mom_capacitor

.subckt mysterious_device vss vcc vn vp
xi6[5] vp vn vss vcc mom_capacitor
xi6[4] vp vn vss vcc mom_capacitor
xi6[3] vp vn vss vcc mom_capacitor
xi6[2] vp vn vss vcc mom_capacitor
xi6[1] vp vn vss vcc mom_capacitor
xi6[0] vp vn vss vcc mom_capacitor
.ends mysterious_device