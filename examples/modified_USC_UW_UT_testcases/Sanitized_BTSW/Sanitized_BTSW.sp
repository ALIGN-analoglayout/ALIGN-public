************************************************************************
* auCdl Netlist:
* 
* Library Name:  ADC_Layout
* Top Cell Name: BTSW
* View Name:     schematic
* Netlisted on:  Jun 11 11:26:41 2019
************************************************************************

*.BIPOLAR
*.RESI = 2000 
*.RESVAL
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
*.LDD
*.SCALE METER
.PARAM



************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_BTSW AVDD AVSS CKSBT CKSBTB VBTSW VIN
*.PININFO CKSBT:I CKSBTB:I VIN:I AVDD:B AVSS:B VBTSW:B
MM9 VBTSW net7 net12 net12 pch l=LA w=WA m=1 nfin=4 nf=2
MM8 AVDD VBTSW net12 net12 pch l=LA w=WA m=1 nfin=4 nf=2
MM7 net7 CKSBT AVDD AVDD pch l=LA w=WA m=1 nfin=4 nf=2
MM10 net013 net12 net013 AVSS nch l=LB w=WC m=4 nfin=4 nf=2
MM6 net27 CKSBTB AVSS AVSS nch l=LA w=WB m=1 nfin=4 nf=2
MM5 VBTSW AVDD net27 AVSS nch l=LA w=WB m=1 nfin=4 nf=2
MM3 VIN VBTSW net013 AVSS nch l=LA w=WB m=1 nfin=4 nf=2
MM2 net7 VBTSW net013 AVSS nch l=LA w=WB m=1 nfin=4 nf=2
MM1 net013 CKSBTB AVSS AVSS nch l=LA w=WB m=1 nfin=4 nf=2
MM0 net7 CKSBT net013 AVSS nch l=LA w=WB m=1 nfin=4 nf=2
.ENDS

