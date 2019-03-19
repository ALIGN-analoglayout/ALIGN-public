import json
import argparse

def translatePlacerResults( placer_results, *, x_shift=None, y_shift=None, ux_ratio=None, uy_ratio=None):
#
# x_shift, y_shift are not scaled by ux_ratio, uy_ratio
#

  if x_shift is None:
    x_shift = 2
  if y_shift is None:
    y_shift = 0
  if ux_ratio is None:
    ux_ratio = 1
  if uy_ratio is None:
    uy_ratio = 8

  def scaleBBox( bbox, offsetX=0, offsetY=0):
    return [ bbox[0]*ux_ratio+offsetX, bbox[1]*uy_ratio+offsetY, bbox[2]*ux_ratio+offsetX, bbox[3]*uy_ratio+offsetY]

  result = dict(placer_results.items())
  result['bbox'] = scaleBBox( placer_results['bbox'])
  result['bbox'][2] += 2*x_shift
  result['bbox'][3] += 2*y_shift

  result['leaves'] = []
  for leaf in placer_results['leaves']:
    d = dict(leaf.items())
    d['bbox'] = scaleBBox( leaf['bbox'])
    d['terminals'] = []
    for terminal in leaf['terminals']:
      dd = dict(terminal.items())
      dd['rect'] = scaleBBox( terminal['rect'])
      d['terminals'].append( dd)
    result['leaves'].append( d)

  result['instances'] = []
  for inst in placer_results['instances']:
    d = dict(inst.items())
    d['transformation'] = dict(inst['transformation'])
    d['transformation']['oX'] *= ux_ratio
    d['transformation']['oX'] += x_shift
    d['transformation']['oY'] *= uy_ratio
    d['transformation']['oY'] += y_shift
    result['instances'].append(d)

  result['terminals'] = []
  for terminal in placer_results['terminals']:
    d = dict(terminal.items())
    d['rect'] = scaleBBox( terminal['rect'], offsetX=x_shift, offsetY=y_shift)
    result['terminals'].append(d)

  return result

if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Translate and scale placer output.")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-ox", "--x_shift", type=int, default=None)
  parser.add_argument( "-oy", "--y_shift", type=int, default=None)
  parser.add_argument( "-sx", "--ux_ratio", type=int, default=None)
  parser.add_argument( "-sy", "--uy_ratio", type=int, default=None)
  args = parser.parse_args()

  block = args.block_name

  with open( block + "_placer_out.json", "rt") as fp:
    placer_results = json.load( fp)

  with open( block + "_placer_out_scaled.json", "wt") as fp:
    fp.write( json.dumps( translatePlacerResults( placer_results, x_shift=args.x_shift, y_shift=args.y_shift, ux_ratio=args.ux_ratio, uy_ratio=args.uy_ratio), indent=2) + "\n")

    
