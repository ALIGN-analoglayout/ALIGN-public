from itertools import accumulate
import contours

def p( v):
  n = len(v)
  a = [0] + v
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

  else:
    samples = [2*(x+0.5)/nx - 1 for x in range(nx)]

    xc = []
    xc.append( [0] * nx)
    xc.append( samples)
    xc.append( [ -x for x in samples])
# a(x-x0)^2 -> 2a(x-x0) <= 1 -> a <= 1/(2(1-x0))
    for x0 in [0.0, 0.2, 0.4, 0.6, 0.8]:
      a = 1.0/(2.0*(1.0-x0))
      xc.append( [ a*(x-x0)*(x-x0) for x in samples])
      xc.append( [ -a*(x-x0)*(x-x0) for x in samples])
      xc.append( [ a*(-x-x0)*(-x-x0) for x in samples])
      xc.append( [ -a*(-x-x0)*(-x-x0) for x in samples])
    yc = [ [-0.5,0.5], [0.5,-0.5], [0,0] ]


  pairs = list(product( xc, yc))

  print( pairs)

  v = [1,1,2,2,3,3]
  assert len(v) == nx

  lst = list(p(v))

  best = []
  best_data = []
  for perm in lst:
    worst = None
    for (sx,sy) in pairs:
      diff = 0
      for (idx,dev) in enumerate(perm):
        for y in range(ny):
          x = idx if y == 0 else nx-1-idx

          tmp = sx[x] + sy[y]

          if dev == 1:
#            print( dev,x,y,sx[x],sy[y],tmp)
            diff += tmp
          elif dev == 2:
#            print( dev,x,y,sx[x],sy[y],tmp)
            diff -= tmp


#      print( "diff", perm, diff, sx, sy)

      if worst is None or abs(diff) > worst:
        worst = abs(diff)
        worst_pair = (sx,sy)

    assert worst is not None
    print( "*", "%.4f" % worst, perm, worst_pair)

    if len(best) == 0 or worst == best[0]: # abs(worst-best[0]) < 0.000001:
#      print( "found best (same):", best, worst)
      best.append( worst)
      best_data.append( (perm,worst,worst_pair))

    elif len(best) == 0 or worst < best[0]:
#      print( "found best:", best, worst)
      best = [worst]
      best_data = [(perm,worst,worst_pair)]


  for tuple in best_data:
    print( "%.4f" % tuple[1], tuple[0])

def test_one():
  v = [1,1,2,2,3,3]
  lst = list(p(v))    
  assert len(lst) == 90

def test_two():
  v = [1,2,3]
  lst = list(p(v))    
  assert len(lst) == 6

def test_three():
  v = [1,2,3,4,5,6]
  lst = list(p(v))    
  assert len(lst) == 720

if __name__ == "__main__":
  a()
