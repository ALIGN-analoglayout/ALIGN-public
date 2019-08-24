import json

def main():

    with open( "__json-90", "rt") as fp:
        frames = json.load( fp)

    step = 50

    trunks = { "ina": [8,16],
               "inb": [8,16],
               "outa": [8,16],
               "outb": [8,16]}

    def metric( x, m, M):
      if x < m:
          return m-x
      elif x > M:
          return x-M
      else:
          return 0

    def distanceToATrunk( actual, m, M):
      if actual in trunks:
        xs = trunks[actual]
        return min( metric( x, m, M) for x in xs) 
      else:
        return None

    sort_indices = []
    for (idx,frame) in enumerate(frames):
        dist = 0
        tbl = {}
        for instance in frame:
            assert instance['w'] % step == 0
            assert instance['h'] % step == 0

            transformation = instance['transformation']
            assert transformation['oX'] % step == 0
            assert transformation['oY'] % step == 0
            assert transformation['sX'] == 1
            assert transformation['sY'] == 1

            llx = transformation['oX']/step
            lly = transformation['oY']/step
            urx = llx + instance['w']/step
            ury = lly + instance['h']/step

            for actual in instance['formal_actual_map'].values():
                d = distanceToATrunk( actual, llx, urx)
                if d is not None:
                  dist += d

                if actual not in tbl:
                    tbl[actual] = (llx,urx)
                else:
                    (m,M) = tbl[actual]
                    if llx < m:
                        m = llx
                    if M < urx:
                        M = urx
                    tbl[actual] = (m,M)

        total = sum( M-m for (m,M) in tbl.values())
        print( idx, tbl, total, dist)
        sort_indices.append( (idx, dist, total))



    sorted_frames = [ frames[idx] for (idx, dist, total) in sorted(sort_indices, key=lambda p: (p[1], p[2], p[0]))]

    with open( "__json-90-sorted", "wt") as fp:
      fp.write( json.dumps( sorted_frames, indent=2) + '\n')

if __name__ == "__main__":
    main()
