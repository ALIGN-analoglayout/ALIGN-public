from itertools import accumulate
import contours

def knuth_lexical_permute( v):
  n = len(v)
  a = [0] + list(sorted(v))
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


from itertools import product
from gstools import SRF, Gaussian


def a(): 
  nx = 6
  ny = 2

  if False:
    xc = contours.contours( nx, 2, 1)
    yc = contours.contours( ny, 1, 1)

    xc = [ [0] + list(accumulate( list(q))) for q in xc]
    yc = [ [0] + list(accumulate( list(q))) for q in yc]

    xc = [ [ (x0+x1)/2.0 for (x0,x1) in zip(q[:-1],q[1:])] for q in xc]
    yc = [ [ (y0+y1)/2.0 for (y0,y1) in zip(q[:-1],q[1:])] for q in yc]

    xc = [ [ qq - (max(q)+min(q))/2.0 for qq in q] for q in xc]
    yc = [ [ qq - (max(q)+min(q))/2.0 for qq in q] for q in yc]

    def fs():
      for (sx,sy) in product( xc, yc):
        def f(x,y):
          return sx[x] + sy[y]
        yield f

  elif False:
    samples = [2*(x+0.5)/nx - 1 for x in range(nx)]

    xc = []
    xc.append( [0] * nx)
    xc.append( samples)
    xc.append( [ -x for x in samples])
# a(x-x0)^2 -> 2a(x-x0) <= 1 -> a <= 1/(2(1-x0))
    for x0 in [0.0, -0.2, -0.4, -0.6, -0.8]:
      a = 1.0/(2.0*(1.0-x0))
      print(a)
      xc.append( [ a*xx*xx for x in samples for xx in [x-x0]])
      xc.append( [ -a*xx*xx for x in samples for xx in [x-x0]])
      xc.append( [ a*xx*xx for x in samples for xx in [-x-x0]])
      xc.append( [ -a*xx*xx for x in samples for xx in [-x-x0]])
    yc = [ [-0.5,0.5], [0.5,-0.5], [0,0] ]

    def fs():
      for (sx,sy) in product( xc, yc):
        def f(x,y):
          return sx[x] + sy[y]
        yield f

  else:
    scale = 20
    model = Gaussian(dim=2,var=1,len_scale=scale)
    def fs():
      for seed in range(256):
        srf = SRF(model,seed=seed)
        def f(x,y):
          # 0 -> -1, 4 -> 1
          # 0 -> -.25, 1 -> .25
          return srf((x*.5-1.0,y*.5-.25))
        print( seed)
        yield f
    fs_lst = list(fs())

  v = [1,1,2,2,3,3]
  assert len(v) == nx

  lst = list(knuth_lexical_permute(v))
  print(len(lst))

  best = []
  best_data = []
  for perm in lst:
    print(perm)
    worst = None
    for f in fs_lst:

      diff = 0
      for (idx,dev) in enumerate(perm):
        for y in range(ny):
          x = idx if y == 0 else nx-1-idx

          tmp = f(x,y)

          if dev == 1:
            diff += tmp
          elif dev == 2:
            diff -= tmp

      if worst is None or abs(diff) > worst:
        worst = abs(diff)
        worst_f = f

    assert worst is not None

    best_data.append( (worst, perm, worst_f))

  for tuple in sorted( best_data):
    print( "%.4f" % tuple[0], tuple[1])

def test_one():
  v = [1,1,2,2,3,3]
  lst = list(knuth_lexical_permute(v))    
  assert len(lst) == 90

def test_two():
  v = [1,2,3]
  lst = list(knuth_lexical_permute(v))    
  assert len(lst) == 6

def test_three():
  v = [1,2,3,4,5,6]
  lst = list(knuth_lexical_permute(v))    
  assert len(lst) == 720

def test_three_unsorted():
  v = [1,2,6,5,3,4]
  lst = list(knuth_lexical_permute(v))    
  assert len(lst) == 720

if __name__ == "__main__":
  a()
