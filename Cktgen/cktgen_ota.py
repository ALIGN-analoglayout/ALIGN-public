from cktgen import *

if __name__ == "__main__":

  args,tech = parse_args()

  ndual = ADT( tech, "ndual", npp=12, nr=1)
  ndual.addM1Terminal( "d1", 1)
  ndual.addM1Terminal( "g1", 3)
  ndual.addM1Terminal( "s1", 5)
  ndual.addM1Terminal( "s2", 7)
  ndual.addM1Terminal( "g2", 9)
  ndual.addM1Terminal( "d2", 11)

  ndualss = ADT( tech, "ndualss", npp=10, nr=1)
  ndualss.addM1Terminal( "d1", 1)
  ndualss.addM1Terminal( "g1", 3)
  ndualss.addM1Terminal( "s", 5)
  ndualss.addM1Terminal( "g2", 7)
  ndualss.addM1Terminal( "d2", 9)

  ncap = ADT( tech, "ncap", npp=4, nr=1)
  ncap.addM1Terminal( "d1", 1)
  ncap.addM1Terminal( "s", 3)

# python cktgen.py --block_name mydesign

  def xg( x): 
    return tech.pitchPoly*tech.halfXGRGrid*2*x
  def yg( y): 
    return tech.pitchDG  *tech.halfYGRGrid*2*y

  def mirrorAcrossYAxis( adt):
    return ADITransform.mirrorAcrossYAxis().preMult( ADITransform.translate( adt.bbox.urx, 0))    

  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(6), yg(7)))

  adnetl =  ADNetlist( args.block_name)
  

  adnetl.addInstance( ADI( ncap, "L1_MM4_MM3", ADITransform.translate(    xg(1), yg(3))))
  adnetl.addInstance( ADI( ndualss, "L1_MM1_MM0", ADITransform.translate( xg(1), yg(1))))

  adnetl.addInstance( ADI( ndual, "L1_MM9_MM8", ADITransform.translate(   xg(3), yg(5))))
  adnetl.addInstance( ADI( ndual, "L1_MM7_MM6", ADITransform.translate(   xg(3), yg(3))))
  adnetl.addInstance( ADI( ndual, "L1_MM10_MM2", ADITransform.translate(  xg(3), yg(1))))

  adnetl.connect('L1_MM1_MM0','g1','Vinp') #1,1

  adnetl.connect('L1_MM7_MM6','s1','net13') #3,3
  adnetl.connect('L1_MM9_MM8','d1','net13') #3,5

  adnetl.connect('L1_MM7_MM6','d2','Voutp') #3,3
  adnetl.connect('L1_MM10_MM2','d2','Voutp') #3,1

  adnetl.connect('L1_MM7_MM6','d1','Voutn') #3,3
  adnetl.connect('L1_MM10_MM2','d1','Voutn') #3,1

  adnetl.connect('L1_MM10_MM2','s1','net10') #3,1  
  adnetl.connect('L1_MM1_MM0','d1','net10') #1,1

  adnetl.connect('L1_MM9_MM8','s1','vdd!') #3,5
  adnetl.connect('L1_MM9_MM8','s2','vdd!') #3,5

  adnetl.connect('L1_MM10_MM2','g1','Vbiasn') #3,1  
  adnetl.connect('L1_MM10_MM2','g2','Vbiasn') #3,1

  adnetl.connect('L1_MM10_MM2','s2','net11') #3,1 
  adnetl.connect('L1_MM1_MM0','d2','net11') #1,1

  adnetl.connect('L1_MM9_MM8','g1','Vbiasp2') #3,5 
  adnetl.connect('L1_MM9_MM8','g2','Vbiasp2') #3,5

  adnetl.connect('L1_MM7_MM6','g1','Vbiasp1') #3,3
  adnetl.connect('L1_MM7_MM6','g2','Vbiasp1') #3,3

  adnetl.connect('L1_MM4_MM3','s','gnd!') #1,4

  adnetl.connect('L1_MM7_MM6','s2','net12') #3,3
  adnetl.connect('L1_MM9_MM8','d2','net12') #3,5

  adnetl.connect('L1_MM1_MM0','s','net6') #1,1
  adnetl.connect('L1_MM4_MM3','d2','net6') #1,4 

  adnetl.connect('L1_MM1_MM0','g2','Vinn') #1,1

  adnetl.connect('L1_MM4_MM3','d1','net1') #1,4 

  adnetl.genNetlist( netl)


  netl.newGR( 'net13', Rect( 3, 3, 3, 5), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'Voutp', Rect( 4, 1, 4, 3), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'Voutn', Rect( 3, 1, 3, 3), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'net10', Rect( 1, 1, 4, 1), "metal2", tech.halfWidthM2[0]*2)
  netl.newGR( 'net11', Rect( 1, 1, 4, 1), "metal2", tech.halfWidthM2[0]*2)
  netl.newGR( 'net12', Rect( 4, 3, 4, 5), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'net6',  Rect( 1, 1, 1, 4), "metal3", tech.halfWidthM3[0]*2)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm)
  netl.write_files( tech, "INPUT", args)
