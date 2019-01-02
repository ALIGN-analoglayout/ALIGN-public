import json
import argparse

def translatePlacerResults( placer_results):
  x_shift = 2
  uy_ratio = 8

  def scaleBBox( bbox, offsetX=0):
    return [ bbox[0]+offsetX, bbox[1]*uy_ratio, bbox[2]+offsetX, bbox[3]*uy_ratio]

  result = dict(placer_results.items())
  result['bbox'] = scaleBBox( placer_results['bbox'], offsetX=0)
  result['bbox'][2] += 2*x_shift

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
    d['transformation']['oX'] += x_shift
    d['transformation']['oY'] *= uy_ratio
    result['instances'].append(d)

  result['terminals'] = []
  for terminal in placer_results['terminals']:
    d = dict(terminal.items())
    d['rect'] = scaleBBox( terminal['rect'], offsetX=x_shift)
    result['terminals'].append(d)

  return result

if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Translate and scale placer output.")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  args = parser.parse_args()

  block = args.block_name

  with open( block + "_placer_out.json", "rt") as fp:
    placer_results = json.load( fp)

  with open( block + "_placer_out_scaled.json", "wt") as fp:
    fp.write( json.dumps( translatePlacerResults( placer_results), indent=2) + "\n")

    
