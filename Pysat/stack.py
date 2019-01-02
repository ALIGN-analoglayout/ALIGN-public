
import json

def load( fn):
  with open( fn, "rt") as fp:
    j = json.load( fp)

  assert len(j['leaves']) == 1

  print( j['nm'], j['bbox'], j['leaves'][0]['template_name'])

  return j

def main():
  mirrors = load("mirrors_placer_out.json")
  dp1x = load("dp1x_placer_out.json")
  dp2x = load("dp2x_placer_out.json")
  dp4x = load("dp4x_placer_out.json")

  


if __name__ == "__main__":
  main()
