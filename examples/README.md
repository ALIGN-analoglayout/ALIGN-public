
### Stacked Transistors
A stacked-transistor array shall be defined and instantiated as below where stack size is 3 and array size is 4: 
```
.SUBCKT pmos_stack_of_three d g s b
.PARAMS m=1
Mi0 d  g n0 b pmos m=m w=90n l=14nm
Mi1 n0 g n1 b pmos m=m w=90n l=14nm
Mi2 n1 g s  b pmos m=m w=90n l=14nm
.ENDS
Xi0 d g s b pmos_stack_of_three m=4
```
