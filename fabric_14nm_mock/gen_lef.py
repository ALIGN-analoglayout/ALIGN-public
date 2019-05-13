import sys
import json

def json_lef(input_json,out_lef,cell_pin):
  macro_name = out_lef + '.lef'
  #cell_pin  = map(str, sys.argv[3].strip('[]').split(','))
  with open( input_json, "rt") as fp:
    j = json.load( fp)

  def s( x):
    return "%.4f" % (x/10000.0)

  with open( macro_name, "wt") as fp:

    #macro_name = "macro_name"

    fp.write( "MACRO %s\n" % out_lef)
    fp.write( "  ORIGIN 0 0 ;\n")
    fp.write( "  FOREIGN %s 0 0 ;\n" % out_lef)

    fp.write( "  SIZE %s BY %s ;\n" % ( s(j['bbox'][2]), s(j['bbox'][3])))

    #for i in ["S","D","G"]:
    for i in cell_pin:
      fp.write( "  PIN %s\n" % i)
        #fp.write( "    DIRECTION %s ;\n" % obj['ported'])
      fp.write( "    DIRECTION INOUT ;\n")
      fp.write( "    USE SIGNAL ;\n")
      fp.write( "    PORT\n")
      for obj in j['terminals']:
        if obj['pin'] in [i]:                  
          fp.write( "      LAYER %s ;\n" % obj['layer'])
          fp.write( "        RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
      fp.write( "    END\n")
      fp.write( "  END %s\n" % i)
    fp.write( "  OBS\n")
    for obj in j['terminals']:
      #if "pin" not in obj and obj['layer'] not in ["via0","via1","via2","poly","LISD","SDT","fin","polycon","GCUT","active","nselect","pselect","nwell"]:
      if obj['pin'] not in cell_pin and obj['layer'] not in ["via0","via1","via2","poly","LISD","SDT","RVT","M0","fin","polycon","GCUT","active","nselect","pselect","nwell"]:
        fp.write( "    LAYER %s ;\n" % obj['layer'])
        fp.write( "      RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
    fp.write( "  END\n")    

    fp.write( "END %s\n" % out_lef)
