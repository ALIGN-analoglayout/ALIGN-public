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
Notes:  
The condition above is necessary but not sufficient for achieving a feasible solution. Example (A, C, B), (B, C, A):  
```
A X X  
X C X  
X X B 
```

