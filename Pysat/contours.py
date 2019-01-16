from itertools import product
import argparse

if __name__ == "__main__":

    parser = argparse.ArgumentParser( description="Generate all discrete contours.")
    parser.add_argument( "-n", "--num_points", type=int, default=4)
    parser.add_argument( "-c", "--curvature_limit", type=int, default=1)
    parser.add_argument( "-s", "--num_slopes", type=int, default=1)

    args = parser.parse_args()

    tl = [ list(range(-args.num_slopes,args.num_slopes+1))] * args.num_points
    
    def ok( t):
        return all( abs(x-y) <= args.curvature_limit for (x,y) in zip(t[1:],t[:-1]))

    ll = [ t for t in product( *tl) if ok(t)]

    print(ll)
    print(len(ll))
