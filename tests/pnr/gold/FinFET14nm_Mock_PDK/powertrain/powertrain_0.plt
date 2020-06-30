#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 1, #Terminals= 2, #Nets= 2, Area=6.56947e+07, HPWL= 3680 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-15842:15842]

set yrange [-50:15842]

set label "mmp0" at 2080 , 7896 center 

set label "B" at 2080 , 14952


set label "D" at 1760 , 6384


set label "G" at 1920 , 7896


set label "S" at 1600 , 6216


set label "vout" at 0 , 6384 center 

set label "vg" at 0 , 7896 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block mmp0 select 0 bsize 4
	160	168
	160	15624
	4000	15624
	4000	168
	160	168


EOF
	232	14920
	232	14984
	3928	14984
	3928	14920
	232	14920

	1720	432
	1720	12336
	1800	12336
	1800	432
	1720	432

	1880	1944
	1880	13848
	1960	13848
	1960	1944
	1880	1944

	1560	264
	1560	12168
	1640	12168
	1640	264
	1560	264


EOF

	-20	6364
	-20	6404
	20	6404
	20	6364
	-20	6364

	-20	7876
	-20	7916
	20	7916
	20	7876
	-20	7876

EOF

#Net: vout
	1760	6384
	0	6384
	1760	6384


#Net: vg
	1920	7896
	0	7896
	1920	7896


EOF

pause -1 'Press any key'