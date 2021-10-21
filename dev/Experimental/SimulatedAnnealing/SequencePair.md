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
Note: For `( s1 A s2 B s3 ), ( s4 A s5 B s6 )`, there can never be a C that is below A and above B (or viceversa).

Proof:

Blocks below A: `(s2 ∪ s3) ∩ s4`  
Blocks above A: `(s5 ∪ s6) ∩ s1`  
Blocks below B: `(s4 ∪ s5) ∩ s3`  
Blocks above B: `(s1 ∪ s2) ∩ s6`  
Blocks below A and above B: `((s2 ∪ s3) ∩ s4) ∩ ((s1 ∪ s2) ∩ s6) = ∅`  
Blocks below B and above A: `((s4 ∪ s5) ∩ s3) ∩ ((s5 ∪ s6) ∩ s1) = ∅`  
No blocks is (below A and above B) OR (below B and above A) 

&nbsp;
### align .. A, .. , B, .. left (llx_a = llx_b)
```
(A is above B) OR ( A is below B) 
( s1 A s2 B s3 ), ( s4 B s5 A s6 )
( s1 B s2 A s3 ), ( s4 A s5 B s6 )
```
