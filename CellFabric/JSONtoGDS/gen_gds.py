import json

import argparse

if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Convert json to GDS (txt format.)")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-j", "--json_file_name", type=str, required=True)

  args = parser.parse_args()

  gds_layer_tbl = { "nwell" : 1,
                    "fin" : 2, 	
                    "poly" : 7, 	
                    "GCUT" : 10,
                    "ndiff" : 11,	
                    "SDT" : 88,	
                    "NSELECT" : 12,
                    "PSELECT" : 13,
                    "SLVT" : 97,	
                    "LVT" : 98,	
                    "SRAMDRC" : 99,
                    "SRAMVT" : 110,
                    "DUMMY" : 8,
                    "polycon" : 16,
                    "LISD" : 17,
                    "via0" : 18,	
                    "metal1" : 19,
                    "via1" : 21,
                    "metal2" : 20,
                    "via2" : 25,
                    "metal3" : 30,
                    "V3" : 35,
                    "M4" : 40,
                    "V4" : 45,
                    "M5" : 50,
                    "V5" : 55,
                    "M6" : 60,
                    "V6" : 65,
                    "M7" : 70,
                    "V7" : 75,
                    "M8" : 80,
                    "V8" : 85,
                    "M9" : 90,
                    "V9" : 95,
                    "Pad" : 96,
                    "BOUNDARY" : 100
                  }

  with open( args.json_file_name, "rt") as fp:
    j = json.load( fp)

  def s( x):
    return "%.3f" % (x/1000.0)

  with open( "__gds", "wt") as fp:

    macro_name = args.block_name

    fp.write( """header 5
bgnlib 118 12 3 13 11 31 118 12 3 13 13 55
libname "pcell"
units 0.00025 2.5e-10
bgnstr 118 12 3 13 13 55 69 12 31 18 0 0
    strname "M3_M2_CDNS_543864435520"
    boundary
        layer 25
        datatype 0
        xy   5   -36 -36   36 -36   36 36   -36 36
                 -36 -36
        endel
    boundary
        layer 20
        datatype 0
        xy   5   -56 -36   56 -36   56 36   -56 36
                 -56 -36
        endel
    boundary
        layer 30
        datatype 0
        xy   5   -36 -56   36 -56   36 56   -36 56
                 -36 -56
        endel
    endstr
bgnstr 118 12 3 13 13 55 69 12 31 18 0 0
    strname "M2_M1_CDNS_543864435521"
    boundary
        layer 21
        datatype 0
        xy   5   -36 -36   36 -36   36 36   -36 36
                 -36 -36
        endel
    boundary
        layer 19
        datatype 0
        xy   5   -36 -56   36 -56   36 56   -36 56
                 -36 -56
        endel
    boundary
        layer 20
        datatype 0
        xy   5   -56 -36   56 -36   56 36   -56 36
                 -56 -36
        endel
    endstr
bgnstr 118 12 3 13 5 58 118 12 3 13 12 43
""")

    fp.write( "    strname \"%s\"\n" % macro_name)

    ordering = [ (0,1), (0,3), (2,3), (2,1), (0,1)]

    for obj in j['terminals']:
        if obj['layer'] in ["via1","via2"]: continue
        fp.write( "    boundary\n")
        fp.write( "        layer %s\n" % gds_layer_tbl[obj['layer']])
        fp.write( "        datatype 0\n")
        fp.write( "        xy 5")
        for p in ordering:
            fp.write( " %d %d" % (obj['rect'][p[0]],obj['rect'][p[1]]))
        fp.write( "\n")
        fp.write( "        endel\n")


    via_tbl = { "via1": "M2_M1_CDNS_543864435521", "via2": "M3_M2_CDNS_543864435520"}
 
    for obj in j['terminals']:
        if obj['layer'] not in ["via1","via2"]: continue
        xc = (obj['rect'][0]+obj['rect'][2])//2
        yc = (obj['rect'][1]+obj['rect'][3])//2

        fp.write( "    sref\n")
        fp.write( "        sname \"%s\"\n" % via_tbl[obj['layer']])
        fp.write( "        xy 1 %d %d\n" % (xc,yc))
        fp.write( "        endel\n")

    fp.write( "    boundary\n")
    fp.write( "        layer 235\n")
    fp.write( "        datatype 5\n")
    fp.write( "        xy 5")
    for p in ordering:
        fp.write( " %d %d" % (j['bbox'][p[0]],j['bbox'][p[1]]))
    fp.write( "\n")
    fp.write( "        propattr 126\n")
    fp.write( "        propvalue \"oaBoundary:pr\"\n")
    fp.write( "        endel\n")
    fp.write( "    endstr\n")

    fp.write( "endlib\n")
