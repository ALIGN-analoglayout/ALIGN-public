import json
from collections import OrderedDict
def json_lef(input_json,out_lef,cell_pin):

  macro_name = out_lef + '.lef'

  def s( x):
    return "%.4f" % (x/10000.0)
  #### Start: This part converting all negative coordinates into positive 
  with open( input_json, "rt") as fp:
    j = json.load(fp, object_pairs_hook=OrderedDict)
  
  x0 = 10*j['bbox'][0]
  y0 = 10*j['bbox'][1]
  j['bbox'][0] = 0
  j['bbox'][1] = 0
  j['bbox'][2] = 10*j['bbox'][2] - x0
  j['bbox'][3] = 10*j['bbox'][3] - y0

  for obj in j['terminals']:
    obj['rect'][0] = 10*obj['rect'][0] - x0
    obj['rect'][1] = 10*obj['rect'][1] - y0
    obj['rect'][2] = 10*obj['rect'][2] - x0
    obj['rect'][3] = 10*obj['rect'][3] - y0

  with open(input_json, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')
 
  #### End:

  with open( input_json, "rt") as fp:
    j = json.load( fp)
  
  with open( macro_name, "wt") as fp:

    #macro_name = "macro_name"

    fp.write( "MACRO %s\n" % out_lef)
    fp.write( "  ORIGIN 0 0 ;\n")
    fp.write( "  FOREIGN %s 0 0 ;\n" % out_lef)

    fp.write( "  SIZE %s BY %s ;\n" % ( s(j['bbox'][2]), s(j['bbox'][3])))
    exclude_layers ={"via0","via1","via2","poly","LISD","SDT","fin","polycon","GCUT","active","nselect","pselect","nwell"}
    #for i in ["S","D","G"]:
    for i in cell_pin:
      fp.write( "  PIN %s\n" % i)
        #fp.write( "    DIRECTION %s ;\n" % obj['ported'])
      fp.write( "    DIRECTION INOUT ;\n")
      fp.write( "    USE SIGNAL ;\n")
      fp.write( "    PORT\n")
      for obj in j['terminals']:
        if 'pin' in obj and obj['pin'] == i:               
          fp.write( "      LAYER %s ;\n" % obj['layer'])
          fp.write( "        RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
          ### Check Pins are on grid or not
          if obj['layer'] == 'M2':
            assert (obj['rect'][1] + 160)%84 == 0, "M2 pin is not on grid"
            assert (j['bbox'][3] - obj['rect'][1] - 160)%84 == 0, "M2 pin is not on grid from top cell boundary; can't flip it"
          if obj['layer'] == 'M1' or obj['layer'] == 'M3':
            assert (obj['rect'][0] + 200)%80 == 0, "M1 pin is not on grid"
            assert (j['bbox'][2] - obj['rect'][0] - 200)%80 == 0, "M1 pin is not on grid from right side; can't mirror it"         
      fp.write( "    END\n")
      fp.write( "  END %s\n" % i)
    fp.write( "  OBS\n")
    for obj in j['terminals']:
      if ('pin' not in obj or obj['pin'] not in cell_pin) and obj['layer'] not in exclude_layers: 
        fp.write( "    LAYER %s ;\n" % obj['layer'])
        fp.write( "      RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
    fp.write( "  END\n")    

    fp.write( "END %s\n" % out_lef)
