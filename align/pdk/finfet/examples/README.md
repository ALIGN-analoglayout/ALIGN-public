
## Transistor Basics
A transistor shall include either w or nfin parameter where w (nfin) refers to the width (the number of fins) in planar (finfet) process.
```
# A transistor in a planar process (Three instances of two-fingered transistor)
Mi0 d g s b pmos w=90n l=14nm m=3 nf=2
```
```
# A transistor in a finfet process (Four instances of two-fingered transistor)
Mi0 d g s b pmos nfin=4 l=14nm m=4 nf=2
```


## Parallel Transistors
An array of transistors in parallel can be specified using m and nf parameters. m specifies the number of instances. nf is required, should be even and specifies the number of fingers for each instance.
```
# Four instances of single-finger transistors in a planar process (total of 4 fingers)
Mi0 d g s b pmos w=90n l=14nm m=2 nf=2
```
```
# Four instances of two-fingered transistors in a planar process (total of 8 fingers)
Mi0 d g s b pmos w=90n l=14nm m=4 nf=2
```

## Series (stacked) Transistors
An array of transistors in series can be specified as a subcircuit where nf is optional and should be one. Only even number of transistors can be stacked. m specified in the instantiation of this subcircuit specifies the number of instances.
```
# Four transistors stacked 
.SUBCKT stack_of_four_p d g s b
Mi0 d  g n0 b p w=90n l=14nm m=1
Mi1 n0 g n1 b p w=90n l=14nm m=1
Mi2 n1 g n2 b p w=90n l=14nm m=1
Mi3 n2 g s  b p w=90n l=14nm m=1
.ENDS
# Three instances of stacked transistor 
Xi0 d g s b pmos_stack_of_three m=3
```
