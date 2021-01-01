.subckt nlvt_s_pcell_0 d g s b
mi1 d g inet1 b nlvt w=180e-9 l=40e-9 m=1 nf=1 
mi2 inet1 g inet2 b nlvt w=180e-9 l=40e-9 m=1 nf=1 
mi3 inet2 g inet3 b nlvt w=180e-9 l=40e-9 m=1 nf=1 
mi4 inet3 g inet4 b nlvt w=180e-9 l=40e-9 m=1 nf=1 
mi5 inet4 g inet5 b nlvt w=180e-9 l=40e-9 m=1 nf=1 
mi6 inet5 g s b nlvt w=180e-9 l=40e-9 m=1 nf=1 
.ends nlvt_s_pcell_0

.subckt plvt_s_pcell_1 d g s b
mi8 inet7 g s b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi7 inet6 g inet7 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi6 inet5 g inet6 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi5 inet4 g inet5 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi4 inet3 g inet4 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi3 inet2 g inet3 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi2 inet1 g inet2 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi1 d g inet1 b plvt w=360e-9 l=40e-9 m=1 nf=1 
.ends plvt_s_pcell_1

.subckt plvt_s_pcell_2 d g s b
mi4 inet3 g s b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi3 inet2 g inet3 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi2 inet1 g inet2 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi1 d g inet1 b plvt w=360e-9 l=40e-9 m=1 nf=1 
.ends plvt_s_pcell_2

.subckt plvt_s_pcell_3 d g s b
mi4 inet3 g s b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi3 inet2 g inet3 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi2 inet1 g inet2 b plvt w=360e-9 l=40e-9 m=1 nf=1 
mi1 d g inet1 b plvt w=360e-9 l=40e-9 m=1 nf=1 
.ends plvt_s_pcell_3

.subckt test_vga_inv_als in in_b vcca vssa
mqn1 in_b in vssa vssa nlvt w=180e-9 l=40e-9 m=1 nf=2
mqp1 in_b in vcca vcca plvt w=180e-9 l=40e-9 m=1 nf=2
.ends test_vga_inv_als

.subckt test_vga_buf_als in out vcca vssa
xi1 net7 out vcca vssa test_vga_inv_als
xi0 in net7 vcca vssa test_vga_inv_als
.ends test_vga_buf_als

.subckt test_vga cmfb_p1 gain_ctrl[1] gain_ctrl[0] iref vcca vinn vinp voutn voutp vssa
xmn29 net093 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn13 net0102 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn30 net092 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn27 net0101 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn31 net091 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn32 net090 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn15 net0103 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
xmn28 net0100 cmfb_p1 vssa vssa nlvt_s_pcell_0 m=1
mmn16 voutp vcca net0103 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn211 voutn gain_ctrl_bf[1] net093 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn221 voutn gain_ctrl_bf[1] net092 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn23 voutn gain_ctrl_bf[0] net091 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn14 voutp gain_ctrl_bf[0] net0102 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn19 voutp gain_ctrl_bf[1] net0101 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn20 voutp gain_ctrl_bf[1] net0100 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
mmn24 voutn vcca net090 vssa nlvt w=1.62e-6 l=40e-9 m=1 nf=6
xmp21 voutp vinn net078 vcca plvt_s_pcell_1 m=4
xmp20 voutn vinp net078 vcca plvt_s_pcell_1 m=4
xmp19 voutp vinn net076 vcca plvt_s_pcell_1 m=4
xmp18 voutn vinp net076 vcca plvt_s_pcell_1 m=4
xmp5 voutp vinn net88 vcca plvt_s_pcell_1 m=4
xmp4 voutn vinp net88 vcca plvt_s_pcell_1 m=4
xmp12 voutp vinn net86 vcca plvt_s_pcell_1 m=4
xmn0 voutn vinp net86 vcca plvt_s_pcell_1 m=4
xmn6 iref iref vcca vcca plvt_s_pcell_2 m=2
xmp14 net0104 iref vcca vcca plvt_s_pcell_3 m=3
xmp01 net0105 iref vcca vcca plvt_s_pcell_3 m=3
xmp3 net99 iref vcca vcca plvt_s_pcell_3 m=3
xmp0 net100 iref vcca vcca plvt_s_pcell_3 m=3
xinv1[1] gain_ctrl_bf[1] gain_ctrlb_bf[1] vcca vssa test_vga_inv_als
xinv1[0] gain_ctrl_bf[0] gain_ctrlb_bf[0] vcca vssa test_vga_inv_als
xbuf1[1] gain_ctrl[1] gain_ctrl_bf[1] vcca vssa test_vga_buf_als
xbuf1[0] gain_ctrl[0] gain_ctrl_bf[0] vcca vssa test_vga_buf_als
mmp10 net078 gain_ctrlb_bf[1] net0104 vcca pulvt w=1.44e-6 l=40e-9 m=1 nf=4
mmp91 net076 gain_ctrlb_bf[1] net0105 vcca pulvt w=1.44e-6 l=40e-9 m=1 nf=4
mmp6 net88 gain_ctrlb_bf[0] net99 vcca pulvt w=1.44e-6 l=40e-9 m=1 nf=4
mmp2 net86 vssa net100 vcca pulvt w=1.44e-6 l=40e-9 m=1 nf=4
.ends test_vga
