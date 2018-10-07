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
  
#left and right
  for i in range(n-2-k):
    sx = 0
    sy = n-2-i
    fx = n-1
    fy = n-2-k-i
    adnetl.addInstance( ADI( ndev, ("un%d" % i), ADITransform.translate( xg(sx), yg(sy))))
    adnetl.addInstance( ADI( pdev, ("up%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(n-1), yg(n-2-k-i)))))

    for (f,a) in [('g','i'),('d','o'),('s','z')]:
      adnetl.connect( 'un%d' % i, f, ('%s%d' % (a,i)))
      adnetl.connect( 'up%d' % i, f, ('%s%d' % (a,i)))

#top and bot
  for i in range(n-2-k):
    sy = 0
    fy = n-1
    sx = n-2-i
    fx = n-2-k-i

    adnetl.addInstance( ADI( ndev, ("vn%d" % i), ADITransform.translate( xg(sx), yg(sy))))
    adnetl.addInstance( ADI( pdev, ("vp%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(fx), yg(fy)))))

    for (f,a) in [('g','a'),('d','b'),('s','c')]:
      adnetl.connect( 'vn%d' % i, f, ('%s%d' % (a,i)))
      adnetl.connect( 'vp%d' % i, f, ('%s%d' % (a,i)))

  adnetl.genNetlist( netl)

  hly = "metal4"
  hWidth = tech.halfWidthM4[0]*2
  vly = "metal5"
  vWidth = tech.halfWidthM5[0]*2

  for i in range(n-2-k):
    sx = 0
    fx = n-1
    mx = n-2-i
    sy = n-2-i
    fy = n-2-k-i

    for p in ['i','o','z']:
      netl.newGR( ('%s%d' % (p,i)), Rect( sx, sy, mx, sy), hly, hWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( mx, sy, mx, fy), vly, vWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( mx, fy, fx, fy), hly, hWidth)

  for i in range(n-2-k):
    sy = 0
    fy = n-1
    my = n-2-i-k
    sx = n-2-i
    fx = n-2-k-i

    for p in ['a','b','c']:
      netl.newGR( ('%s%d' % (p,i)), Rect( sx, sy, sx, my), vly, vWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( sx, my, fx, my), hly, hWidth)
      netl.newGR( ('%s%d' % (p,i)), Rect( fx, my, fx, fy), vly, vWidth)



  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm)
  netl.write_files( tech, "INPUT", args)
