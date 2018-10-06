from cktgen import *

if __name__ == "__main__":

  args,tech = parse_args()

  ndev = ADT( tech, "n",npp=6,nr=1)
  ndev.addM1Terminal( "s", 1)
  ndev.addM1Terminal( "g", 3)
  ndev.addM1Terminal( "d", 5)

  pdev = ADT( tech, "p",npp=6,nr=1)
  pdev.addM1Terminal( "s", 1)
  pdev.addM1Terminal( "g", 3)
  pdev.addM1Terminal( "d", 5)

# python cktgen.py --block_name mydesign

  def xg( x): 
    return tech.pitchPoly*tech.halfXGRGrid*2*x
  def yg( y): 
    return tech.pitchDG  *tech.halfYGRGrid*2*y

  def mirrorAcrossYAxis( adt):
    return ADITransform.mirrorAcrossYAxis().preMult( ADITransform.translate( adt.bbox.urx, 0))    


#  n = 18
#  k = (n-2)//2
  k = 3
  n = 2*k+2


  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(n), yg(n)))

  adnetl =  ADNetlist( args.block_name)
  
# 1,8
# 1,7
# 1,6
# 1,5
#              8,4
#              8,3
#              8,2
#              8,1

#left and right
  for i in range(n-2-k):
    adnetl.addInstance( ADI( ndev, ("un%d" % i), ADITransform.translate( xg(0), yg(n-2-i))))
    adnetl.addInstance( ADI( pdev, ("up%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(n-1), yg(n-2-k-i)))))

    dev = 'un%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

    dev = 'up%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

#top and bot
  for i in range(n-2-k):
    adnetl.addInstance( ADI( ndev, ("vn%d" % i), ADITransform.translate( xg(n-2-i), yg(0))))
    adnetl.addInstance( ADI( pdev, ("vp%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(n-2-k-i), yg(n-1)))))

    dev = 'vn%d' % i
    adnetl.connect( dev,'g',('a%d' % i))
    adnetl.connect( dev,'d',('b%d' % i))
    adnetl.connect( dev,'s',('c%d' % i))

    dev = 'vp%d' % i
    adnetl.connect( dev,'g',('a%d' % i))
    adnetl.connect( dev,'d',('b%d' % i))
    adnetl.connect( dev,'s',('c%d' % i))

  adnetl.genNetlist( netl)

  hly = "metal4"
  hWidth = tech.halfWidthM4[0]*2
  vly = "metal5"
  vWidth = tech.halfWidthM5[0]*2

  for i in range(n-2-k):
    mx = n-2-i
    sy = n-2-i
    fy = n-2-k-i

    for p in ['i','o','z']:
      netl.newGR( ('%s%d' % (p,i)), Rect( 0,  sy, mx,  sy), hly, hWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( mx, sy, mx,  fy), vly, vWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( mx, fy, n-1, fy), hly, hWidth)

  for i in range(n-2-k):
    my = n-2-i-k
    sx = n-2-i
    fx = n-2-k-i

    for p in ['a','b','c']:
      netl.newGR( ('%s%d' % (p,i)), Rect( sx, 0,  sx, my),  vly, vWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( sx, my, fx, my),  hly, hWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( fx, my, fx, n-1), vly, vWidth)



  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm)
  netl.write_files( tech, "INPUT", args)
