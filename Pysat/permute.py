
from collections import OrderedDict

#v = [1,1,2,2,3,3]
#v = [1,1,1,1,2,2,2,2,3,3,3,3]
v = [1,2,3,4,4,5,5,5,5]
n = len(v)
a = [0] + v

def p():
  while True:
    yield a[1:]
    j = n-1
    while a[j] >= a[j+1]:
      j -= 1

    if j == 0: return

    l = n
    while a[j] >= a[l]:
      l -= 1
    a[l],a[j] = a[j],a[l]

    a[j+1:] = a[n:j:-1]


tbl = OrderedDict()

for l in p():
  t = tuple(l)
  assert t not in tbl
  tbl[t] = l

print( len(tbl))
