import sys
import json

def gen_lef_data(data, fp, macro_name, cell_pin):
  def s( x):
    return "%.4f" % (x/10000.0)

  fp.write( "MACRO %s\n" % macro_name)
  fp.write( "  ORIGIN 0 0 ;\n")
  fp.write( "  FOREIGN %s 0 0 ;\n" % macro_name)

  fp.write( "  SIZE %s BY %s ;\n" % ( s(data['bbox'][2]), s(data['bbox'][3])))

  exclude_layers = {"via0","via1","via2","poly","LISD","SDT","RVT","M0","fin","polycon","GCUT","active","nselect","pselect","nwell"}

# O(npins * nsegments) algorithm. Could be O(npins + nsegments) FIX!

  for i in cell_pin:
    fp.write( "  PIN %s\n" % i)
    #fp.write( "    DIRECTION %s ;\n" % obj['ported'])
    fp.write( "    DIRECTION INOUT ;\n")
    fp.write( "    USE SIGNAL ;\n")
    fp.write( "  PORT\n")
    for obj in data['terminals']:
      if 'pin' in obj:
        print( obj['pin'], i)
        if obj['pin'] == i:                  
          fp.write( "      LAYER %s ;\n" % obj['layer'])
          fp.write( "        RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
    fp.write( "    END\n")
    fp.write( "  END %s\n" % i)

  fp.write( "  OBS\n")
  for obj in data['terminals']:
    if ('pin' not in obj or obj['pin'] not in cell_pin) and obj['layer'] not in exclude_layers:
      fp.write( "    LAYER %s ;\n" % obj['layer'])
      fp.write( "      RECT %s %s %s %s ;\n" % tuple( [ s(x) for x in obj['rect']]))
  fp.write( "  END\n")    

  fp.write( "END %s\n" % macro_name)

def gen_lef_json_fp( json_fp, lef_fp, macro_name, cell_pin):
  gen_lef_data( json.load( json_fp), lef_fp, macro_name, cell_pin)

def gen_lef_json( json_fn, lef_fn, macro_name, cell_pin):
  with open( json_fn, "rt") as json_fp, \
       open( lef_fn, "wt") as fp:
    gen_lef_json_fp( json_fp, lef_fp, macro_name, cell_pin)

  
