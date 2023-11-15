.subckt buf y a
* @: Generator(name='black_box')
.ends buf

.subckt inv y a
* @: Generator(name='black_box')
.ends inv

.subckt nand y a b
* @: Generator(name='black_box')
.ends nand

.subckt fixed_height z a b c d
x0 y0 a b nand
x1 y1 c d nand
x2 y2 y0 y1 nand
x3 y3 y2 inv
x4 z y3 buf
.ends fixed_height
