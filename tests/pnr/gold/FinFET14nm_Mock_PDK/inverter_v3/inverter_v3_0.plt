#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 3, #Terminals= 2, #Nets= 2, Area=1.80634e+07, HPWL= 5464 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-4530:4530]

set yrange [-50:4530]

set label "mp1" at 800 , 2016 center 

set label "B" at 800 , 3192


set label "D" at 640 , 504


set label "G" at 640 , 2016


set label "S" at 800 , 336


set label "mn1" at 2240 , 2016 center 

set label "B" at 2240 , 3192


set label "D" at 2080 , 504


set label "G" at 2080 , 2016


set label "S" at 2240 , 336


set label "mn2" at 3680 , 2016 center 

set label "B" at 3680 , 3192


set label "D" at 3520 , 504


set label "S" at 3360 , 1176


set label "vout" at 640 , 0 center 

set label "vin" at 0 , 2016 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block mp1 select 0 bsize 4
	160	168
	160	3864
	1440	3864
	1440	168
	160	168

# block mn1 select 0 bsize 4
	1600	168
	1600	3864
	2880	3864
	2880	168
	1600	168

# block mn2 select 0 bsize 4
	3040	168
	3040	3864
	4320	3864
	4320	168
	3040	168


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

	1672	3160
	1672	3224
	2808	3224
	2808	3160
	1672	3160

	1848	472
	1848	536
	2312	536
	2312	472
	1848	472

	1848	1984
	1848	2048
	2312	2048
	2312	1984
	1848	1984

	2008	304
	2008	368
	2472	368
	2472	304
	2008	304

	3112	3160
	3112	3224
	4248	3224
	4248	3160
	3112	3160

	3288	472
	3288	536
	3752	536
	3752	472
	3288	472

	3320	264
	3320	2088
	3400	2088
	3400	264
	3320	264


EOF

	620	-20
	620	20
	660	20
	660	-20
	620	-20

	-20	1996
	-20	2036
	20	2036
	20	1996
	-20	1996

EOF

#Net: vout
	640	504
	2080	504
	640	504

	640	504
	3520	504
	640	504

	640	504
	640	0
	640	504


#Net: vin
	640	2016
	2080	2016
	640	2016

	640	2016
	0	2016
	640	2016


EOF

pause -1 'Press any key'