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



#
# m(y)xn(x) grid of devices in each quadrant
#



# m,n = 2,2
#          x01 x11
#          x00 x10
#  x10 x00
#  x11 x01
# 

  m = 3
  n = 3

  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(2*n+1), yg(2*m+1)))

  adnetl =  ADNetlist( args.block_name)
  
  for i in range(m):
    uy = m+1+i
    vy = m-1-i
    for j in range(n):
      ux = n+1+j
      adnetl.addInstance( ADI( ndev, ("un%d_%d" % (i,j)), ADITransform.translate( xg(ux), yg(uy))))        
      for (f,a) in [('g','a0'),('d','b0'),('s','c0')]:
        adnetl.connect( 'un%d_%d' % (i,j), f, ('%s' % a))

      vx = n-1-j
      adnetl.addInstance( ADI( ndev, ("vn%d_%d" % (i,j)), mirrorAcrossYAxis( ndev).preMult( ADITransform.translate( xg(vx), yg(vy)))))        
      for (f,a) in [('g','a0'),('d','b0'),('s','c0')]:
        adnetl.connect( 'vn%d_%d' % (i,j), f, ('%s' % a))

  adnetl.genNetlist( netl)

  hly = "metal2"
  hWidth = tech.halfWidthM2[0]*2
  vly = "metal3"
  vWidth = tech.halfWidthM3[0]*2


  for p in ['a0','b0','c0']:
    netl.newGR( ('%s' % p), Rect( m, 0, m, m+1+m-1), vly, vWidth)

  for i in range(m):
    uy = m+1+i
    vy = m-1-i

    for p in ['a0','b0','c0']:
      netl.newGR( ('%s' % p), Rect( m, uy, m+1+m-1, uy), hly, hWidth)
      netl.newGR( ('%s' % p), Rect( 0, vy, m,       vy), hly, hWidth)        





  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
