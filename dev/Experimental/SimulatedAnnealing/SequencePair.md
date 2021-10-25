## Sequence Pair Legalization with Constraints

### order .., A, .., B, .. left_to_right
```
(A should always proceed B)
( s1 A s2 B s3 ), ( s4 A s5 B s6 )
```

&nbsp;
### order with abut .., A, B, .. left_to_right
```
(A should always proceed B) AND (C cannot be in between => s2 ∩ s5 = ∅)
( s1 A s2 B s3 ), ( s4 A s5 B s6 )
```

&nbsp;
### order .. , A, .., B, .. top_to_bottom
```
(A should always be above B)
( s1 A s2 B s3 ), ( s4 B s5 A s6 )
```

&nbsp;
### order with abut .., A, B, .. top_to_bottom
```
(A should always be above B) AND (C cannot be below A and above B => s2 ∩ s5 = ∅)
( s1 A s2 B s3 ), ( s4 B s5 A s6 )
```

&nbsp;
### align .., A, .., B, ..  bottom (lly_a = lly_b)
```
(A is either right or left of B)
( s1 A s2 B s3 ), ( s4 A s5 B s6 )
( s1 B s2 A s3 ), ( s4 B s5 A s6 )
```
Notes:  
The condition above is necessary but not sufficient for achieving a feasible solution. Example (A, C, B), (A, C, B):  
```
A X X  
X C X  
X X B 
```

&nbsp;
### align .. A, .. , B, .. left (llx_a = llx_b)
```
(A is above B) OR ( A is below B) 
( s1 A s2 B s3 ), ( s4 B s5 A s6 )
( s1 B s2 A s3 ), ( s4 A s5 B s6 )
```
Note: For `( s1 A s2 B s3 ), ( s4 B s5 A s6 )`, there can never be a C that is right of A and left of B.

Proof:

Blocks left of A: `(s2 ∪ s3) ∩ s6`  
Blocks right of A: `(s4 ∪ s5) ∩ s1`  
Blocks left  of B: `(s1 ∪ s2) ∩ s4`  
Blocks right  of B: `(s5 ∪ s6) ∩ s3`  
Blocks right of A AND left of B: `((s2 ∪ s3) ∩ s6) ∩ ((s1 ∪ s2) ∩ s4) as s4 and s6 are disjoint`  
Blocks right of A AND left of B: `((s4 ∪ s5) ∩ s1) ∩ ((s5 ∪ s6) ∩ s3) as s1 and s3 are disjoint`
