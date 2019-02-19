from cktgen.cktgen import *

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


  n = 12

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

  for i in range(n-2):
    adnetl.addInstance( ADI( ndev, ("un%d" % i), ADITransform.translate( xg(0), yg(n-1-i))))
    adnetl.addInstance( ADI( pdev, ("up%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(n-1), yg(n-3-i)))))

    dev = 'un%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

    dev = 'up%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

  adnetl.genNetlist( netl)

  hly = "metal4"
  hWidth = tech.halfWidthM4[0]*2
  vly = "metal5"
  vWidth = tech.halfWidthM5[0]*2

  for i in range(n-2):
    netl.newGR( ('i%d' % i), Rect( 0,     n-1-i, n-2-i, n-1-i), hly, hWidth)
    netl.newGR( ('i%d' % i), Rect( n-2-i, n-1-i, n-2-i, n-3-i), vly, vWidth)
    netl.newGR( ('i%d' % i), Rect( n-2-i, n-3-i, n-1,   n-3-i), hly, hWidth)

    netl.newGR( ('o%d' % i), Rect( 0,     n-1-i, n-2-i, n-1-i), hly, hWidth)
    netl.newGR( ('o%d' % i), Rect( n-2-i, n-1-i, n-2-i, n-3-i), vly, vWidth)
    netl.newGR( ('o%d' % i), Rect( n-2-i, n-3-i, n-1,   n-3-i), hly, hWidth)

    netl.newGR( ('z%d' % i), Rect( 0,     n-1-i, n-2-i, n-1-i), hly, hWidth)
    netl.newGR( ('z%d' % i), Rect( n-2-i, n-1-i, n-2-i, n-3-i), vly, vWidth)
    netl.newGR( ('z%d' % i), Rect( n-2-i, n-3-i, n-1,   n-3-i), hly, hWidth)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
