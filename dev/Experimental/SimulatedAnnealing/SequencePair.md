## Sequence Pair Legalization with Constraints

### order .., A, .., B, .. left_to_right
```
(A should always proceed B)
( .. A .. B .. ), ( .. A .. B .. )
```

&nbsp;
### order with abut .., A, B, .. left_to_right
```
(A should always proceed B) AND (C cannot be in between => set1 ∩ set2 = ∅)
( .. A .. set1 .. B .. ), (.. A .. set2 .. B .. )
```

&nbsp;
### order .. , A, .., B, .. top_to_bottom
```
(A should always be above B)
( .. A .. B .. ), ( .. B .. A .. )
```

&nbsp;
### order with abut .., A, B, .. top_to_bottom```
```
(A should always be above B) AND (C cannot be in between => set1 ∩ set2 = ∅)
( .. A .. set1 .. B .. ), ( .. B .. set2 .. A .. )
```

&nbsp;
### align .., A, .., B, ..  bottom (lly_a = lly_b)
```
(A is either right or left of B) AND (C cannot be above and below => set1 ∩ set4 = set2 ∩ set3 = ∅)
( set1 A set2 B set3 ), ( set4 A set5 B set6 )
( set1 B set2 A set3 ), ( set4 B set5 A set6 )
```
For `( set1 A set2 B set3 ), ( set4 A set5 B set6 )`: 
Blocks below A: `(set2 ∪ set3) ∩ set4` 
Blocks above A: `(set5 ∪ set6) ∩ set1` 
Blocks below B: `(set4 ∪ set5) ∩ set3` 
Blocks above B: `(set1 ∪ set2) ∩ set6` 
Blocks below A and above B: `((set2 ∪ set3) ∩ set4) ∩ ((set1 ∪ set2) ∩ set6) = ∅` 
Blocks below B and above A: `((set4 ∪ set5) ∩ set3) ∩ ((set5 ∪ set6) ∩ set1) = ∅` 
No blocks is (below A and above B) OR (below B and above A) 

&nbsp;
### align .. A, .. , B, .. left (llx_a = llx_b)
```
(A is above B) AND (C cannot left of one and right of the other => ...)
( .. A .. B .. ), ( .. B .. A .. )
OR
(A is below B) AND (C cannot left of one and right of the other => ...)
( .. B .. A .. ), ( .. A .. B .. )
```
