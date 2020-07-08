#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 1, #Terminals= 2, #Nets= 2, Area=4.62336e+07, HPWL= 320 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-6930:6930]

set yrange [-50:6930]

set label "mn2_mn1_mp2_mp1" at 3440 , 3360 center 

set label "G1" at 160 , 168


set label "G2" at 160 , 168


set label "SN" at 160 , 168


set label "SP" at 160 , 168


set label "vout" at 0 , 168 center 

set label "vin" at 0 , 168 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block mn2_mn1_mp2_mp1 select 0 bsize 4
	160	168
	160	6552
	6720	6552
	6720	168
	160	168


EOF
	160	168
	160	168
	160	168
	160	168
	160	168

	160	168
	160	168
	160	168
	160	168
	160	168

	160	168
	160	168
	160	168
	160	168
	160	168

	160	168
	160	168
	160	168
	160	168
	160	168


EOF

	-20	148
	-20	188
	20	188
	20	148
	-20	148

	-20	148
	-20	188
	20	188
	20	148
	-20	148

EOF

#Net: vout
	160	168
	0	168
	160	168


#Net: vin
	160	168
	0	168
	160	168


EOF

pause -1 'Press any key'