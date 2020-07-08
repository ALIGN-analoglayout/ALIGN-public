#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 6, #Terminals= 3, #Nets= 10, Area=1.06848e+08, HPWL= 48356 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-12650:12650]

set yrange [-50:12650]

set label "m20_m21_m19_m18" at 4240 , 10584 center 

set label "B" at 1920 , 8568


set label "DA" at 1920 , 8568


set label "DB" at 1920 , 8568


set label "DC" at 1920 , 8568


set label "DD" at 1920 , 8568


set label "GB" at 1920 , 8568


set label "S" at 1920 , 8568


set label "m29_m30_m17" at 4240 , 2184 center 

set label "B" at 2560 , 168


set label "DA" at 2560 , 168


set label "DB" at 2560 , 168


set label "DC" at 2560 , 168


set label "S" at 2560 , 168


set label "m22_m25" at 7520 , 6216 center 

set label "B" at 7520 , 7392


set label "DA" at 7200 , 5460


set label "DB" at 7520 , 4872


set label "S" at 7520 , 4536


set label "m23_m24" at 960 , 6216 center 

set label "B" at 960 , 7392


set label "DA" at 1280 , 5460


set label "DB" at 960 , 4872


set label "S" at 960 , 4536


set label "m33_m32" at 960 , 10080 center 

set label "B" at 960 , 11256


set label "DA" at 640 , 9324


set label "DB" at 960 , 8736


set label "S" at 960 , 8400


set label "m31_m27_m26" at 4240 , 6384 center 

set label "B" at 2080 , 4368


set label "DA" at 2080 , 4368


set label "DB" at 2080 , 4368


set label "DC" at 2080 , 4368


set label "SA" at 2080 , 4368


set label "SB" at 2080 , 4368


set label "SC" at 2080 , 4368


set label "vout" at 0 , 8736 center 

set label "vcm" at 0 , 8568 center 

set label "ibias" at 2560 , 0 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block m20_m21_m19_m18 select 0 bsize 4
	1920	8568
	1920	12600
	6560	12600
	6560	8568
	1920	8568

# block m29_m30_m17 select 0 bsize 4
	2560	168
	2560	4200
	5920	4200
	5920	168
	2560	168

# block m22_m25 select 0 bsize 4
	6720	4368
	6720	8064
	8320	8064
	8320	4368
	6720	4368

# block m23_m24 select 0 bsize 4
	1760	4368
	1760	8064
	160	8064
	160	4368
	1760	4368

# block m33_m32 select 0 bsize 4
	160	8232
	160	11928
	1760	11928
	1760	8232
	160	8232

# block m31_m27_m26 select 0 bsize 4
	2080	4368
	2080	8400
	6400	8400
	6400	4368
	2080	4368


EOF
	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	1920	8568
	1920	8568
	1920	8568
	1920	8568
	1920	8568

	2560	168
	2560	168
	2560	168
	2560	168
	2560	168

	2560	168
	2560	168
	2560	168
	2560	168
	2560	168

	2560	168
	2560	168
	2560	168
	2560	168
	2560	168

	2560	168
	2560	168
	2560	168
	2560	168
	2560	168

	2560	168
	2560	168
	2560	168
	2560	168
	2560	168

	6792	7360
	6792	7424
	8248	7424
	8248	7360
	6792	7360

	7160	4632
	7160	6288
	7240	6288
	7240	4632
	7160	4632

	7288	4840
	7288	4904
	7752	4904
	7752	4840
	7288	4840

	7128	4504
	7128	4568
	7912	4568
	7912	4504
	7128	4504

	1688	7360
	1688	7424
	232	7424
	232	7360
	1688	7360

	1320	4632
	1320	6288
	1240	6288
	1240	4632
	1320	4632

	1192	4840
	1192	4904
	728	4904
	728	4840
	1192	4840

	1352	4504
	1352	4568
	568	4568
	568	4504
	1352	4504

	232	11224
	232	11288
	1688	11288
	1688	11224
	232	11224

	600	8496
	600	10152
	680	10152
	680	8496
	600	8496

	728	8704
	728	8768
	1192	8768
	1192	8704
	728	8704

	568	8368
	568	8432
	1352	8432
	1352	8368
	568	8368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368

	2080	4368
	2080	4368
	2080	4368
	2080	4368
	2080	4368


EOF

	-20	8716
	-20	8756
	20	8756
	20	8716
	-20	8716

	-20	8548
	-20	8588
	20	8588
	20	8548
	-20	8548

	2540	-20
	2540	20
	2580	20
	2580	-20
	2540	-20

EOF

#Net: net80
	1920	8568
	7200	5460
	1920	8568


#Net: net84
	1920	8568
	1280	5460
	1920	8568


#Net: vout
	1920	8568
	960	8736
	1920	8568

	1920	8568
	2080	4368
	1920	8568

	1920	8568
	0	8736
	1920	8568


#Net: net77
	1920	8568
	640	9324
	1920	8568

	1920	8568
	2080	4368
	1920	8568


#Net: vcm
	1920	8568
	0	8568
	1920	8568


#Net: net022
	1920	8568
	2560	168
	1920	8568


#Net: ibias
	2560	168
	2560	0
	2560	168


#Net: net039
	2560	168
	2080	4368
	2560	168


#Net: net91
	7520	4872
	2080	4368
	7520	4872


#Net: net92
	960	4872
	2080	4368
	960	4872


EOF

pause -1 'Press any key'