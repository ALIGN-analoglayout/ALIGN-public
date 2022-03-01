.subckt inv i zn sn sp
m0 zn i sn sn nmos w=w0 l=l0
m1 zn i sp sp pmos w=w1 l=l0
.ends inv

.subckt inv_b i zn sn sp pb
m0 zn i sn sn nmos w=w0 l=l0
m1 zn i sp pb pmos w=w1 l=l0
.ends inv_b

.subckt tgate ga gb d s bn bp
m0 d ga s bn nmos w=w l=90n
m1 d gb s bp pmos w=w l=90n
.ends tgate
