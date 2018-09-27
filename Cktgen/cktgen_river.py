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


  n = 32

  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(n+2), yg(n+2)))

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
    adnetl.addInstance( ADI( ndev, ("un%d" % i), ADITransform.translate( xg(1), yg(n-i))))
    adnetl.addInstance( ADI( pdev, ("up%d" % i), mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(n), yg(n-2-i)))))

    dev = 'un%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

    dev = 'up%d' % i
    adnetl.connect( dev,'g',('i%d' % i))
    adnetl.connect( dev,'d',('o%d' % i))
    adnetl.connect( dev,'s',('z%d' % i))

  adnetl.genNetlist( netl)

  for i in range(n-2):
    netl.newGR( ('i%d' % i), Rect( 1, n-i, n-1-i, n-i), "metal2", tech.halfWidthM2[0]*2)
    netl.newGR( ('i%d' % i), Rect( n-1-i, n-i, n-1-i, n-2-i), "metal3", tech.halfWidthM3[0]*2)
    netl.newGR( ('i%d' % i), Rect( n-1-i, n-2-i, n, n-2-i), "metal2", tech.halfWidthM2[0]*2)

    netl.newGR( ('o%d' % i), Rect( 1, n-i, n-1-i, n-i), "metal2", tech.halfWidthM2[0]*2)
    netl.newGR( ('o%d' % i), Rect( n-1-i, n-i, n-1-i, n-2-i), "metal3", tech.halfWidthM3[0]*2)
    netl.newGR( ('o%d' % i), Rect( n-1-i, n-2-i, n, n-2-i), "metal2", tech.halfWidthM2[0]*2)

    netl.newGR( ('z%d' % i), Rect( 1, n-i, n-1-i, n-i), "metal2", tech.halfWidthM2[0]*2)
    netl.newGR( ('z%d' % i), Rect( n-1-i, n-i, n-1-i, n-2-i), "metal3", tech.halfWidthM3[0]*2)
    netl.newGR( ('z%d' % i), Rect( n-1-i, n-2-i, n, n-2-i), "metal2", tech.halfWidthM2[0]*2)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm)
  netl.write_files( tech, "INPUT", args)
