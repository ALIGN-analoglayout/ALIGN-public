#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 7, #Terminals= 6, #Nets= 9, Area=8.08819e+07, HPWL= 32180 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-9490:9490]

set yrange [-50:9490]

set label "MM3" at 800 , 2016 center 

set label "B" at 800 , 3192


set label "G" at 640 , 2016


set label "S" at 480 , 420


set label "MM2" at 800 , 5880 center 

set label "B" at 800 , 7056


set label "D" at 640 , 4368


set label "G" at 640 , 5880


set label "S" at 800 , 4200


set label "MM4" at 2240 , 5880 center 

set label "B" at 2240 , 7056


set label "G" at 2080 , 5880


set label "S" at 1920 , 4284


set label "MM1" at 2240 , 2016 center 

set label "B" at 2240 , 3192


set label "D" at 2080 , 504


set label "G" at 2080 , 2016


set label "S" at 2240 , 336


set label "XI11" at 6000 , 2184 center 

set label "A1" at 3040 , 168


set label "A2" at 3040 , 168


set label "VDD" at 3040 , 168


set label "VSS" at 3040 , 168


set label "ZN" at 3040 , 168


set label "XI5" at 4560 , 6384 center 

set label "I" at 3040 , 4368


set label "VDD" at 3040 , 4368


set label "VSS" at 3040 , 4368


set label "ZN" at 3040 , 4368


set label "XI6" at 7760 , 6384 center 

set label "I" at 6240 , 4368


set label "VDD" at 6240 , 4368


set label "VSS" at 6240 , 4368


set label "ZN" at 6240 , 4368


set label "VRN" at 480 , 0 center 

set label "VRNX" at 0 , 4200 center 

set label "VRP" at 2080 , 0 center 

set label "VRPX" at 2240 , 0 center 

set label "CK" at 3040 , 0 center 

set label "VRCTL" at 3040 , 0 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block MM3 select 0 bsize 4
	160	168
	160	3864
	1440	3864
	1440	168
	160	168

# block MM2 select 0 bsize 4
	160	4032
	160	7728
	1440	7728
	1440	4032
	160	4032

# block MM4 select 0 bsize 4
	1600	4032
	1600	7728
	2880	7728
	2880	4032
	1600	4032

# block MM1 select 0 bsize 4
	1600	168
	1600	3864
	2880	3864
	2880	168
	1600	168

# block XI11 select 0 bsize 4
	3040	168
	3040	4200
	8960	4200
	8960	168
	3040	168

# block XI5 select 0 bsize 4
	3040	4368
	3040	8400
	6080	8400
	6080	4368
	3040	4368

# block XI6 select 0 bsize 4
	6240	4368
	6240	8400
	9280	8400
	9280	4368
	6240	4368


EOF
	232	3160
	232	3224
	1368	3224
	1368	3160
	232	3160

	408	1984
	408	2048
	872	2048
	872	1984
	408	1984

	440	264
	440	576
	520	576
	520	264
	440	264

	232	7024
	232	7088
	1368	7088
	1368	7024
	232	7024

	408	4336
	408	4400
	872	4400
	872	4336
	408	4336

	408	5848
	408	5912
	872	5912
	872	5848
	408	5848

	568	4168
	568	4232
	1032	4232
	1032	4168
	568	4168

	1672	7024
	1672	7088
	2808	7088
	2808	7024
	1672	7024

	1848	5848
	1848	5912
	2312	5912
	2312	5848
	1848	5848

	1880	4128
	1880	4440
	1960	4440
	1960	4128
	1880	4128

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

	3040	168
	3040	168
	3040	168
	3040	168
	3040	168

	3040	168
	3040	168
	3040	168
	3040	168
	3040	168

	3040	168
	3040	168
	3040	168
	3040	168
	3040	168

	3040	168
	3040	168
	3040	168
	3040	168
	3040	168

	3040	168
	3040	168
	3040	168
	3040	168
	3040	168

	3040	4368
	3040	4368
	3040	4368
	3040	4368
	3040	4368

	3040	4368
	3040	4368
	3040	4368
	3040	4368
	3040	4368

	3040	4368
	3040	4368
	3040	4368
	3040	4368
	3040	4368

	3040	4368
	3040	4368
	3040	4368
	3040	4368
	3040	4368

	6240	4368
	6240	4368
	6240	4368
	6240	4368
	6240	4368

	6240	4368
	6240	4368
	6240	4368
	6240	4368
	6240	4368

	6240	4368
	6240	4368
	6240	4368
	6240	4368
	6240	4368

	6240	4368
	6240	4368
	6240	4368
	6240	4368
	6240	4368


EOF

	460	-20
	460	20
	500	20
	500	-20
	460	-20

	-20	4180
	-20	4220
	20	4220
	20	4180
	-20	4180

	2060	-20
	2060	20
	2100	20
	2100	-20
	2060	-20

	2220	-20
	2220	20
	2260	20
	2260	-20
	2220	-20

	3020	-20
	3020	20
	3060	20
	3060	-20
	3020	-20

	3020	-20
	3020	20
	3060	20
	3060	-20
	3020	-20

EOF

#Net: CLK
	640	2016
	2080	2016
	640	2016

	640	2016
	3040	4368
	640	2016

	640	2016
	6240	4368
	640	2016


#Net: VRN
	480	420
	640	4368
	480	420

	480	420
	480	0
	480	420


#Net: net010
	640	5880
	3040	168
	640	5880

	640	5880
	6240	4368
	640	5880


#Net: VRNX
	800	4200
	0	4200
	800	4200


#Net: net018
	2080	5880
	3040	4368
	2080	5880


#Net: VRP
	1920	4284
	2080	504
	1920	4284

	1920	4284
	2080	0
	1920	4284


#Net: VRPX
	2240	336
	2240	0
	2240	336


#Net: CK
	3040	168
	3040	0
	3040	168


#Net: VRCTL
	3040	168
	3040	0
	3040	168


EOF

pause -1 'Press any key'