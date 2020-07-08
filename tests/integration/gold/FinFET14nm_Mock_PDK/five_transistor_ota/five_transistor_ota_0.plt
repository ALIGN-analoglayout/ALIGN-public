#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 3, #Terminals= 4, #Nets= 6, Area=2.22566e+07, HPWL= 14692 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-11642:11642]

set yrange [-50:11642]

set label "m5_m4" at 960 , 9744 center 

set label "B" at 960 , 10920


set label "DA" at 640 , 8988


set label "DB" at 960 , 8400


set label "S" at 960 , 8064


set label "m1_m2" at 960 , 2016 center 

set label "B" at 960 , 3192


set label "DA" at 640 , 1260


set label "DB" at 960 , 672


set label "S" at 960 , 336


set label "m3_m0" at 960 , 5880 center 

set label "B" at 960 , 7056


set label "DA" at 640 , 4368


set label "DB" at 960 , 4536


set label "GA" at 640 , 5880


set label "GB" at 960 , 6048


set label "S" at 960 , 4200


set label "id" at 0 , 8988 center 

set label "vout" at 0 , 4368 center 

set label "vinn" at 0 , 5880 center 

set label "vinp" at 1920 , 6048 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block m5_m4 select 0 bsize 4
	160	7896
	160	11592
	1760	11592
	1760	7896
	160	7896

# block m1_m2 select 0 bsize 4
	160	168
	160	3864
	1760	3864
	1760	168
	160	168

# block m3_m0 select 0 bsize 4
	160	4032
	160	7728
	1760	7728
	1760	4032
	160	4032


EOF
	232	10888
	232	10952
	1688	10952
	1688	10888
	232	10888

	600	8160
	600	9816
	680	9816
	680	8160
	600	8160

	728	8368
	728	8432
	1192	8432
	1192	8368
	728	8368

	568	8032
	568	8096
	1352	8096
	1352	8032
	568	8032

	232	3160
	232	3224
	1688	3224
	1688	3160
	232	3160

	600	432
	600	2088
	680	2088
	680	432
	600	432

	728	640
	728	704
	1192	704
	1192	640
	728	640

	568	304
	568	368
	1352	368
	1352	304
	568	304

	232	7024
	232	7088
	1688	7088
	1688	7024
	232	7024

	408	4336
	408	4400
	872	4400
	872	4336
	408	4336

	728	4504
	728	4568
	1192	4568
	1192	4504
	728	4504

	408	5848
	408	5912
	872	5912
	872	5848
	408	5848

	728	6016
	728	6080
	1192	6080
	1192	6016
	728	6016

	568	4168
	568	4232
	1352	4232
	1352	4168
	568	4168


EOF

	-20	8968
	-20	9008
	20	9008
	20	8968
	-20	8968

	-20	4348
	-20	4388
	20	4388
	20	4348
	-20	4348

	-20	5860
	-20	5900
	20	5900
	20	5860
	-20	5860

	1900	6028
	1900	6068
	1940	6068
	1940	6028
	1900	6028

EOF

#Net: id
	640	8988
	0	8988
	640	8988


#Net: net10
	960	8400
	960	4200
	960	8400


#Net: net8
	640	1260
	960	4536
	640	1260


#Net: vout
	960	672
	640	4368
	960	672

	960	672
	0	4368
	960	672


#Net: vinn
	640	5880
	0	5880
	640	5880


#Net: vinp
	960	6048
	1920	6048
	960	6048


EOF

pause -1 'Press any key'