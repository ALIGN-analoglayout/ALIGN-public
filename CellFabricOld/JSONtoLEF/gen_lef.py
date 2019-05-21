import json
if __name__ == "__main__":
  with open( "mydesign_dr_globalrouting_lef_test.json", "rt") as fp:
    j = json.load( fp)

  def s( x):
    return "%.3f" % (x/1000.0)

  with open( "__lef", "wt") as fp:

    macro_name = "macro_name"

    fp.write( "MACRO %s\n" % macro_name)
    fp.write( "  ORIGIN 0 0 ;\n")
    fp.write( "  FOREIGN %s 0 0 ;\n" % macro_name)

    fp.write( "  SIZE %s BY %s ;\n" % ( s(j['bbox'][2]), s(j['bbox'][3])))


    for obj in j['terminals']:
      if "ported" in obj:
        fp.write( "  PIN %s\n" % obj['netName'])
        fp.write( "    DIRECTION %s ;\n" % obj['ported'])
        fp.write( "    USE SIGNAL ;\n")
        fp.write( "    PORT\n")
        fp.write( "      LAYER %s ;\n" % obj['layer'])
        fp.write( "        RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
        fp.write( "    END\n")
        fp.write( "  END %s\n" % obj['netName'])


    fp.write( "  OBS\n")
    for obj in j['terminals']:
      if "ported" not in obj and obj['layer'] not in ["via1","via2"]:
        fp.write( "    LAYER %s ;\n" % obj['layer'])
        fp.write( "      RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
    fp.write( "  END\n")    

    fp.write( "END %s\n" % macro_name)
