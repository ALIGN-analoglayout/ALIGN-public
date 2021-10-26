
### Transistor Basics
A transistor shall include either w or nfin parameter where w (nfin) refers to the width (the number of fins) in planar (finfet) process:
```
# A transistor in a planar process (Four instances of two-fingered transistor)
Mi0 d g s b pmos w=90n l=14nm m=4 nf=2
```
```
# A transistor in a finfet process (Four instances of two-fingered transistor)
Mi0 d g s b pmos nfin=4 l=14nm m=4 nf=2
```
# ALIGN supports transistors with minimum nf=2

### Parallel Transistors
An array of transistors in parallel can be specified using m and nf parameters. m specifies the number of instances. nf is optional and specifies the number of fingers for each instance.
```
# Four instances of single-finger transistors in a planar process (total of 4 fingers)
Mi0 d g s b pmos w=90n l=14nm m=4
```
```
# Four instances of two-fingered transistors in a planar process (total of 8 fingers)
Mi0 d g s b pmos w=90n l=14nm m=4 nf=2
```

### Series (stacked) Transistors
An array of stacked transistors shall be defined and instantiated as below where stack size is 3 and array size is 4: 
```
.SUBCKT stack_of_three_p d g s b
.param m=1
Mi0 d  g n0 b p w=90n l=14nm m=1
Mi1 n0 g n1 b p w=90n l=14nm m=1
Mi2 n1 g s  b p w=90n l=14nm m=1
.ENDS
Xi0 d g s b pmos_stack_of_three m=4
```
