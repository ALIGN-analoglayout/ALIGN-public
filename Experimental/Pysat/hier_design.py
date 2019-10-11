import json

def load( fn, dir='INPUT'):
  with open( fn if dir is None else dir + '/' + fn, "rt") as fp:
    j = json.load( fp)
  return j

def dump( fn, j, dir='INPUT'):
  with open( fn if dir is None else dir + '/' + fn, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')
