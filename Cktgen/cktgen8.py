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


  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(10), yg(10)))

  adnetl =  ADNetlist( args.block_name)
  
  adnetl.addInstance( ADI( ndev, "un0", ADITransform.translate( xg(1), yg(1))))
  adnetl.addInstance( ADI( pdev, "up0", mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(8), yg(8)))))

  adnetl.addInstance( ADI( ndev, "un1", ADITransform.translate( xg(8), yg(1))))
  adnetl.addInstance( ADI( pdev, "up1", mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(1), yg(8)))))

  adnetl.addInstance( ADI( ndev, "un2", ADITransform.translate( xg(5), yg(1))))
  adnetl.addInstance( ADI( pdev, "up2", mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(1), yg(5)))))

  adnetl.addInstance( ADI( ndev, "un3", ADITransform.translate( xg(3), yg(4))))
  adnetl.addInstance( ADI( pdev, "up3", mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(4), yg(3)))))

  adnetl.connect('un0','g','i0')
  adnetl.connect('un0','d','o0')
  adnetl.connect('un0','s','vss')

  adnetl.connect('up0','g','i0')
  adnetl.connect('up0','d','o0')
  adnetl.connect('up0','s','vcc')

  adnetl.connect('un1','g','i1')
  adnetl.connect('un1','d','o1')
  adnetl.connect('un1','s','vss')

  adnetl.connect('up1','g','i1')
  adnetl.connect('up1','d','o1')
  adnetl.connect('up1','s','vcc')

  adnetl.connect('un2','g','i2')
  adnetl.connect('un2','d','o2')
  adnetl.connect('un2','s','vss')

  adnetl.connect('up2','g','i2')
  adnetl.connect('up2','d','o2')
  adnetl.connect('up2','s','vcc')

  adnetl.connect('un3','g','i3')
  adnetl.connect('un3','d','o3')
  adnetl.connect('un3','s','vss')

  adnetl.connect('up3','g','i3')
  adnetl.connect('up3','d','o3')
  adnetl.connect('up3','s','vcc')

  adnetl.genNetlist( netl)

  netl.newGR( 'i0', Rect( 1, 8, 8, 8), "metal4", tech.halfWidthM4[0]*2)
  netl.newGR( 'i0', Rect( 1, 1, 1, 8), "metal3", tech.halfWidthM3[0]*2)

  netl.newGR( 'o0', Rect( 8, 1, 8, 8), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'o0', Rect( 1, 1, 8, 1), "metal4", tech.halfWidthM4[0]*2)

  netl.newGR( 'i1', Rect( 1, 8, 8, 8), "metal4", tech.halfWidthM4[0]*2)
  netl.newGR( 'i1', Rect( 8, 1, 8, 8), "metal3", tech.halfWidthM3[0]*2)

  netl.newGR( 'o1', Rect( 1, 1, 1, 8), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'o1', Rect( 1, 1, 8, 1), "metal4", tech.halfWidthM4[0]*2)

  netl.newGR( 'i2', Rect( 1, 5, 5, 5), "metal4", tech.halfWidthM4[0]*2)
  netl.newGR( 'i2', Rect( 5, 1, 5, 5), "metal3", tech.halfWidthM3[0]*2)

  netl.newGR( 'o2', Rect( 1, 1, 1, 5), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'o2', Rect( 1, 1, 5, 1), "metal4", tech.halfWidthM4[0]*2)

  netl.newGR( 'i3', Rect( 3, 4, 4, 4), "metal4", tech.halfWidthM4[0]*2)
  netl.newGR( 'i3', Rect( 4, 3, 4, 4), "metal3", tech.halfWidthM3[0]*2)

  netl.newGR( 'o3', Rect( 3, 3, 3, 4), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'o3', Rect( 3, 3, 4, 3), "metal4", tech.halfWidthM4[0]*2)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
