#Use this file as a script for gnuplot
#(See http://www.gnuplot.info/ for details)

set title" #Blocks= 8, #Terminals= 3, #Nets= 9, Area=7.67693e+07, HPWL= 55164 "

set nokey
#   Uncomment these two lines starting with "set"
#   to save an EPS file for inclusion into a latex document
# set terminal postscript eps color solid 20
# set output "result.eps"

#   Uncomment these two lines starting with "set"
#   to save a PS file for printing
# set terminal postscript portrait color solid 20
# set output "result.ps"


set xrange [-9010:9010]

set yrange [-50:9010]

set label "m8" at 8160 , 5880 center 

set label "B" at 8160 , 7056


set label "G" at 8000 , 5880


set label "S" at 7840 , 4284


set label "m28" at 800 , 6552 center 

set label "B" at 800 , 7728


set label "D" at 640 , 5040


set label "G" at 640 , 6552


set label "S" at 800 , 4872


set label "m15" at 4960 , 6552 center 

set label "B" at 4960 , 7728


set label "D" at 5120 , 5040


set label "G" at 5120 , 6552


set label "S" at 4960 , 4872


set label "m9" at 8000 , 2016 center 

set label "B" at 8000 , 3192


set label "G" at 7840 , 2016


set label "S" at 7680 , 420


set label "m5_m4_m30_m21" at 2880 , 2352 center 

set label "B" at 320 , 168


set label "DA" at 320 , 168


set label "DB" at 320 , 168


set label "DC" at 320 , 168


set label "DD" at 320 , 168


set label "S" at 320 , 168


set label "m3_m2" at 6560 , 5880 center 

set label "B" at 6560 , 7056


set label "DA" at 6240 , 5124


set label "DB" at 6560 , 4536


set label "S" at 6560 , 4200


set label "m27_m29" at 2880 , 6552 center 

set label "B" at 2880 , 7728


set label "DA" at 3040 , 5880


set label "DB" at 3360 , 5376


set label "SA" at 2240 , 4872


set label "SB" at 3520 , 5040


set label "m1_m0" at 6400 , 2016 center 

set label "B" at 6400 , 3192


set label "DA" at 6080 , 504


set label "DB" at 6400 , 672


set label "GA" at 6080 , 2016


set label "GB" at 6400 , 2184


set label "S" at 6400 , 336


set label "vrefp" at 0 , 5040 center 

set label "ibias" at 320 , 0 center 

set label "vin_vrefp" at 6080 , 0 center 

plot[:][:] '-' with lines linestyle 3, '-' with lines linestyle 7, '-' with lines linestyle 1, '-' with lines linestyle 0

# block m8 select 0 bsize 4
	7520	4032
	7520	7728
	8800	7728
	8800	4032
	7520	4032

# block m28 select 0 bsize 4
	160	4704
	160	8400
	1440	8400
	1440	4704
	160	4704

# block m15 select 0 bsize 4
	5600	4704
	5600	8400
	4320	8400
	4320	4704
	5600	4704

# block m9 select 0 bsize 4
	7360	168
	7360	3864
	8640	3864
	8640	168
	7360	168

# block m5_m4_m30_m21 select 0 bsize 4
	320	168
	320	4536
	5440	4536
	5440	168
	320	168

# block m3_m2 select 0 bsize 4
	5760	4032
	5760	7728
	7360	7728
	7360	4032
	5760	4032

# block m27_m29 select 0 bsize 4
	1600	4704
	1600	8400
	4160	8400
	4160	4704
	1600	4704

# block m1_m0 select 0 bsize 4
	5600	168
	5600	3864
	7200	3864
	7200	168
	5600	168


EOF
	7592	7024
	7592	7088
	8728	7088
	8728	7024
	7592	7024

	7768	5848
	7768	5912
	8232	5912
	8232	5848
	7768	5848

	7800	4128
	7800	4440
	7880	4440
	7880	4128
	7800	4128

	232	7696
	232	7760
	1368	7760
	1368	7696
	232	7696

	408	5008
	408	5072
	872	5072
	872	5008
	408	5008

	408	6520
	408	6584
	872	6584
	872	6520
	408	6520

	568	4840
	568	4904
	1032	4904
	1032	4840
	568	4840

	5528	7696
	5528	7760
	4392	7760
	4392	7696
	5528	7696

	5352	5008
	5352	5072
	4888	5072
	4888	5008
	5352	5008

	5352	6520
	5352	6584
	4888	6584
	4888	6520
	5352	6520

	5192	4840
	5192	4904
	4728	4904
	4728	4840
	5192	4840

	7432	3160
	7432	3224
	8568	3224
	8568	3160
	7432	3160

	7608	1984
	7608	2048
	8072	2048
	8072	1984
	7608	1984

	7640	264
	7640	576
	7720	576
	7720	264
	7640	264

	320	168
	320	168
	320	168
	320	168
	320	168

	320	168
	320	168
	320	168
	320	168
	320	168

	320	168
	320	168
	320	168
	320	168
	320	168

	320	168
	320	168
	320	168
	320	168
	320	168

	320	168
	320	168
	320	168
	320	168
	320	168

	320	168
	320	168
	320	168
	320	168
	320	168

	5832	7024
	5832	7088
	7288	7088
	7288	7024
	5832	7024

	6200	4296
	6200	5952
	6280	5952
	6280	4296
	6200	4296

	6328	4504
	6328	4568
	6792	4568
	6792	4504
	6328	4504

	6168	4168
	6168	4232
	6952	4232
	6952	4168
	6168	4168

	1672	7696
	1672	7760
	4088	7760
	4088	7696
	1672	7696

	3000	5136
	3000	6624
	3080	6624
	3080	5136
	3000	5136

	3128	5344
	3128	5408
	3592	5408
	3592	5344
	3128	5344

	2008	4840
	2008	4904
	2472	4904
	2472	4840
	2008	4840

	3288	5008
	3288	5072
	3752	5072
	3752	5008
	3288	5008

	5672	3160
	5672	3224
	7128	3224
	7128	3160
	5672	3160

	5848	472
	5848	536
	6312	536
	6312	472
	5848	472

	6168	640
	6168	704
	6632	704
	6632	640
	6168	640

	5848	1984
	5848	2048
	6312	2048
	6312	1984
	5848	1984

	6168	2152
	6168	2216
	6632	2216
	6632	2152
	6168	2152

	6008	304
	6008	368
	6792	368
	6792	304
	6008	304


EOF

	-20	5020
	-20	5060
	20	5060
	20	5020
	-20	5020

	300	-20
	300	20
	340	20
	340	-20
	300	-20

	6060	-20
	6060	20
	6100	20
	6100	-20
	6060	-20

EOF

#Net: net030
	8000	5880
	320	168
	8000	5880

	8000	5880
	3040	5880
	8000	5880


#Net: vrefp
	640	5040
	3520	5040
	640	5040

	640	5040
	0	5040
	640	5040


#Net: net26
	640	6552
	320	168
	640	6552

	640	6552
	3360	5376
	640	6552


#Net: net026
	5120	5040
	2240	4872
	5120	5040

	5120	5040
	6400	2184
	5120	5040


#Net: net037
	5120	6552
	7840	2016
	5120	6552

	5120	6552
	6560	4536
	5120	6552

	5120	6552
	6080	504
	5120	6552


#Net: ibias
	320	168
	320	0
	320	168


#Net: net16
	320	168
	6400	336
	320	168


#Net: net14
	6240	5124
	6400	672
	6240	5124


#Net: vin_vrefp
	6080	2016
	6080	0
	6080	2016


EOF

pause -1 'Press any key'