from itertools import product

def contours( n, c, s):
  tl = [ list(range(-s,s+1))] * n
  def ok( t):
    return all( abs(x-y) <= c for (x,y) in zip(t[1:],t[:-1]))
  return [ t for t in product( *tl) if ok(t)]


if __name__ == "__main__":
  import argparse

  parser = argparse.ArgumentParser( description="Generate all discrete contours.")
  parser.add_argument( "-n", "--num_points", type=int, default=4)
  parser.add_argument( "-c", "--curvature_limit", type=int, default=1)
  parser.add_argument( "-s", "--num_slopes", type=int, default=1)

  args = parser.parse_args()

  ll = contours( args.num_points, args.curvature_limit, args.num_slopes)

  print(ll)
  print(len(ll))



