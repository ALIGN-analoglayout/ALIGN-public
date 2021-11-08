.subckt VGA vmirror_vga vin1 vin2 s0 s1 vout_vga1 vout_vga2 vps vgnd

        MCM00 vmirror_vga vmirror_vga n1 vgnd n nfin=12 nf=4
        MCM01 n1 vmirror_vga vgnd vgnd n nfin=12 nf=4

        MCM10 n2 vmirror_vga vgnd vgnd n nfin=12 nf=4
        MCM11 n3 vmirror_vga n2 vgnd n nfin=12 nf=4

        MSW0 vcm0 vps n3 vgnd n nfin=12 nf=4

        MDP00 vout_vga2 vin2 n4 vgnd n nfin=12 nf=4
        MDP01 n4 vin2 vcm0 vgnd n nfin=12 nf=4
        MDP10 vout_vga1 vin1 n5 vgnd n nfin=12 nf=4
        MDP11 n5 vin1 vcm0 vgnd n nfin=12 nf=4


        MCM20 n6 vmirror_vga vgnd vgnd n nfin=12 nf=4
        MCM21 n7 vmirror_vga n6 vgnd n nfin=12 nf=4

        MSW1 vcm1 s0 n7 vgnd n nfin=12 nf=4

        MDP20 vout_vga2 vin2 n8 vgnd n nfin=12 nf=4
        MDP21 n8 vin2 vcm1 vgnd n nfin=12 nf=4
        MDP30 vout_vga1 vin1 n9 vgnd n nfin=12 nf=4
        MDP31 n9 vin1 vcm1 vgnd n nfin=12 nf=4

        MCM30 n10 vmirror_vga vgnd vgnd n nfin=12 nf=4
        MCM31 n11 vmirror_vga n10 vgnd n nfin=12 nf=4

        MSW2 vcm2 s1 n11 vgnd n nfin=12 nf=4

        MDP40 vout_vga2 vin2 n12 vgnd n nfin=12 nf=4
        MDP41 n12 vin2 vcm2 vgnd n nfin=12 nf=4
        MDP50 vout_vga1 vin1 n13 vgnd n nfin=12 nf=4
        MDP51 n13 vin1 vcm2 vgnd n nfin=12 nf=4

        R5 vps vout_vga2 5000
        R6 vps vout_vga1 5000
.ends VGA
