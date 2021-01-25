import json
from collections import OrderedDict
def json_pos(input_json):

  #### Start: This part converting all negative coordinates into positive 
  with open( input_json, "rt") as fp:
    j = json.load(fp, object_pairs_hook=OrderedDict)
  
  x0 = j['bbox'][0]
  y0 = j['bbox'][1]
  j['bbox'][0] = 0
  j['bbox'][1] = 0
  j['bbox'][2] = j['bbox'][2] - x0
  j['bbox'][3] = j['bbox'][3] - y0

  for obj in j['terminals']:
    obj['rect'][0] = obj['rect'][0] - x0
    obj['rect'][1] = obj['rect'][1] - y0
    obj['rect'][2] = obj['rect'][2] - x0
    obj['rect'][3] = obj['rect'][3] - y0

  with open(input_json, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')
 
  #### End:

