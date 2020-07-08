#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 5, #Terminals= 3, #Nets= 6, Area=4.21478e+07, HPWL= 28156 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-8282:8282]

set yrange [-50:8282]

set label "m0" at 800 , 2016 center 

set label "B" at 800 , 3192


set label "D" at 640 , 504


set label "G" at 640 , 2016


set label "S" at 800 , 336


set label "m4" at 800 , 5880 center 

set label "B" at 800 , 7056


set label "G" at 640 , 5880


set label "S" at 480 , 4284


set label "m29_m17_m1" at 3280 , 6048 center 

set label "B" at 1600 , 4032


set label "DA" at 1600 , 4032


set label "DB" at 1600 , 4032


set label "DC" at 1600 , 4032


set label "S" at 1600 , 4032


set label "m3_m2" at 4160 , 2016 center 

set label "B" at 4160 , 3192


set label "DA" at 3840 , 1260


set label "DB" at 4160 , 672


set label "S" at 4160 , 336


set label "m21_m19" at 2400 , 2016 center 

set label "B" at 2400 , 3192


set label "DA" at 2080 , 504


set label "DB" at 2400 , 672


set label "GA" at 2080 , 2016


set label "GB" at 2400 , 2184


set label "S" at 2400 , 336


set label "vfb" at 0 , 4284 center 

set label "ibias" at 0 , 4032 center 

set label "vcm" at 2400 , 0 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block m0 select 0 bsize 4
	160	168
	160	3864
	1440	3864
	1440	168
	160	168

# block m4 select 0 bsize 4
	160	4032
	160	7728
	1440	7728
	1440	4032
	160	4032

# block m29_m17_m1 select 0 bsize 4
	1600	4032
	1600	8064
	4960	8064
	4960	4032
	1600	4032

# block m3_m2 select 0 bsize 4
	3360	168
	3360	3864
	4960	3864
	4960	168
	3360	168

# block m21_m19 select 0 bsize 4
	1600	168
	1600	3864
	3200	3864
	3200	168
	1600	168


EOF
	232	3160
	232	3224
	1368	3224
	1368	3160
	232	3160

	408	472
	408	536
	872	536
	872	472
	408	472

	408	1984
	408	2048
	872	2048
	872	1984
	408	1984

	568	304
	568	368
	1032	368
	1032	304
	568	304

	232	7024
	232	7088
	1368	7088
	1368	7024
	232	7024

	408	5848
	408	5912
	872	5912
	872	5848
	408	5848

	440	4128
	440	4440
	520	4440
	520	4128
	440	4128

	1600	4032
	1600	4032
	1600	4032
	1600	4032
	1600	4032

	1600	4032
	1600	4032
	1600	4032
	1600	4032
	1600	4032

	1600	4032
	1600	4032
	1600	4032
	1600	4032
	1600	4032

	1600	4032
	1600	4032
	1600	4032
	1600	4032
	1600	4032

	1600	4032
	1600	4032
	1600	4032
	1600	4032
	1600	4032

	3432	3160
	3432	3224
	4888	3224
	4888	3160
	3432	3160

	3800	432
	3800	2088
	3880	2088
	3880	432
	3800	432

	3928	640
	3928	704
	4392	704
	4392	640
	3928	640

	3768	304
	3768	368
	4552	368
	4552	304
	3768	304

	1672	3160
	1672	3224
	3128	3224
	3128	3160
	1672	3160

	1848	472
	1848	536
	2312	536
	2312	472
	1848	472

	2168	640
	2168	704
	2632	704
	2632	640
	2168	640

	1848	1984
	1848	2048
	2312	2048
	2312	1984
	1848	1984

	2168	2152
	2168	2216
	2632	2216
	2632	2152
	2168	2152

	2008	304
	2008	368
	2792	368
	2792	304
	2008	304


EOF

	-20	4264
	-20	4304
	20	4304
	20	4264
	-20	4264

	-20	4012
	-20	4052
	20	4052
	20	4012
	-20	4012

	2380	-20
	2380	20
	2420	20
	2420	-20
	2380	-20

EOF

#Net: vfb
	640	504
	800	7056
	640	504

	640	504
	480	4284
	640	504

	640	504
	1600	4032
	640	504

	640	504
	2080	2016
	640	504

	640	504
	0	4284
	640	504


#Net: net84
	640	2016
	640	5880
	640	2016

	640	2016
	4160	672
	640	2016

	640	2016
	2400	672
	640	2016


#Net: ibias
	1600	4032
	0	4032
	1600	4032


#Net: net022
	1600	4032
	2400	336
	1600	4032


#Net: net80
	3840	1260
	2080	504
	3840	1260


#Net: vcm
	2400	2184
	2400	0
	2400	2184


EOF

pause -1 'Press any key'