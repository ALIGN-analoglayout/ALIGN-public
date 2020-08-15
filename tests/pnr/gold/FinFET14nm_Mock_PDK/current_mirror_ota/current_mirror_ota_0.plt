#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 5, #Terminals= 5, #Nets= 8, Area=1.37249e+08, HPWL= 40336 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-11890:11890]

set yrange [-50:11890]

set label "m14_m16" at 5920 , 2016 center 

set label "B" at 5920 , 3192


set label "DA" at 5600 , 1260


set label "DB" at 5920 , 672


set label "S" at 5920 , 336


set label "m11_m10" at 5920 , 5880 center 

set label "B" at 5920 , 7056


set label "DA" at 5600 , 5124


set label "DB" at 5920 , 4536


set label "S" at 5920 , 4200


set label "m19_m18s" at 2240 , 5544 center 

set label "B" at 2240 , 10248


set label "DA" at 1920 , 4788


set label "DB" at 2080 , 4200


set label "S" at 1760 , 3864


set label "m21_m20s" at 9600 , 5544 center 

set label "B" at 9600 , 10248


set label "DA" at 9280 , 4788


set label "DB" at 9440 , 4200


set label "S" at 9120 , 3864


set label "m17_m15" at 5920 , 9744 center 

set label "B" at 5920 , 10920


set label "DA" at 5760 , 8232


set label "DB" at 6080 , 8400


set label "GA" at 5760 , 9744


set label "GB" at 6080 , 9912


set label "S" at 5920 , 8064


set label "id" at 5600 , 0 center 

set label "vbiasnd" at 11840 , 4200 center 

set label "voutp" at 0 , 4200 center 

set label "vinn" at 5760 , 11592 center 

set label "vinp" at 6080 , 11592 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block m14_m16 select 0 bsize 4
	5120	168
	5120	3864
	6720	3864
	6720	168
	5120	168

# block m11_m10 select 0 bsize 4
	4800	4032
	4800	7728
	7040	7728
	7040	4032
	4800	4032

# block m19_m18s select 0 bsize 4
	160	168
	160	10920
	4320	10920
	4320	168
	160	168

# block m21_m20s select 0 bsize 4
	7520	168
	7520	10920
	11680	10920
	11680	168
	7520	168

# block m17_m15 select 0 bsize 4
	4480	7896
	4480	11592
	7360	11592
	7360	7896
	4480	7896


EOF
	5192	3160
	5192	3224
	6648	3224
	6648	3160
	5192	3160

	5560	432
	5560	2088
	5640	2088
	5640	432
	5560	432

	5688	640
	5688	704
	6152	704
	6152	640
	5688	640

	5528	304
	5528	368
	6312	368
	6312	304
	5528	304

	4872	7024
	4872	7088
	6968	7088
	6968	7024
	4872	7024

	5560	4296
	5560	5952
	5640	5952
	5640	4296
	5560	4296

	5688	4504
	5688	4568
	6152	4568
	6152	4504
	5688	4504

	5208	4168
	5208	4232
	6632	4232
	6632	4168
	5208	4168

	232	10216
	232	10280
	4248	10280
	4248	10216
	232	10216

	1880	432
	1880	9144
	1960	9144
	1960	432
	1880	432

	2040	600
	2040	7800
	2120	7800
	2120	600
	2040	600

	1720	264
	1720	7464
	1800	7464
	1800	264
	1720	264

	7592	10216
	7592	10280
	11608	10280
	11608	10216
	7592	10216

	9240	432
	9240	9144
	9320	9144
	9320	432
	9240	432

	9400	600
	9400	7800
	9480	7800
	9480	600
	9400	600

	9080	264
	9080	7464
	9160	7464
	9160	264
	9080	264

	4552	10888
	4552	10952
	7288	10952
	7288	10888
	4552	10888

	5048	8200
	5048	8264
	6472	8264
	6472	8200
	5048	8200

	5368	8368
	5368	8432
	6792	8432
	6792	8368
	5368	8368

	5048	9712
	5048	9776
	6472	9776
	6472	9712
	5048	9712

	5368	9880
	5368	9944
	6792	9944
	6792	9880
	5368	9880

	4888	8032
	4888	8096
	6952	8096
	6952	8032
	4888	8032


EOF

	5580	-20
	5580	20
	5620	20
	5620	-20
	5580	-20

	11820	4180
	11820	4220
	11860	4220
	11860	4180
	11820	4180

	-20	4180
	-20	4220
	20	4220
	20	4180
	-20	4180

	5740	11572
	5740	11612
	5780	11612
	5780	11572
	5740	11572

	6060	11572
	6060	11612
	6100	11612
	6100	11572
	6060	11572

EOF

#Net: id
	5600	1260
	5600	0
	5600	1260


#Net: net24
	5920	672
	5920	8064
	5920	672


#Net: vbiasnd
	5600	5124
	9440	4200
	5600	5124

	5600	5124
	11840	4200
	5600	5124


#Net: voutp
	5920	4536
	2080	4200
	5920	4536

	5920	4536
	0	4200
	5920	4536


#Net: net27
	1920	4788
	6080	8400
	1920	4788


#Net: net16
	9280	4788
	5760	8232
	9280	4788


#Net: vinn
	5760	9744
	5760	11592
	5760	9744


#Net: vinp
	6080	9912
	6080	11592
	6080	9912


EOF

pause -1 'Press any key'