import sys
import json
from collections import OrderedDict
def json_gds(input_json,out_json):  
  #input_json = "./Viewer/INPUT/mydesign_dr_globalrouting.json"
  #out_json = "json_gds.json"
  macro_name = out_json + '.json'
  with open( input_json, "rt") as fp:
    j = json.load(fp, object_pairs_hook=OrderedDict)
  def s( x):
    #return "%.3f" % (x/1000.0)
    return (x*10)
  x0 = int(s(j['bbox'][0]))
  y0 = int(s(j['bbox'][1]))
  j['bbox'][0] = 0
  j['bbox'][1] = 0
  j['bbox'][2] = int(s(j['bbox'][2]) - x0)
  j['bbox'][3] = int(s(j['bbox'][3]) - y0)

  for obj in j['terminals']:
    obj['rect'][0] = int(s(obj['rect'][0]) - x0)
    obj['rect'][1] = int(s(obj['rect'][1]) - y0)
    obj['rect'][2] = int(s(obj['rect'][2]) - x0)
    obj['rect'][3] = int(s(obj['rect'][3]) - y0)
  with open(macro_name, "wt") as fp:
    #fp.write(json.dumps(j))
    fp.write( json.dumps( j, indent=2) + '\n')
  #return 0


    
