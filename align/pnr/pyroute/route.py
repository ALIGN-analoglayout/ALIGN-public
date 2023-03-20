import math
import networkx as nx

from geom import Point, Rect, Transform
from layers import Layers


class Router:
    def __init__(self, src, tgt, obs, layers):
        self._layers = layers
        self._src    = self.findGridPts(src)
        self._tgt    = self.findGridPts(tgt)
        self._obs    = self.snapToGrid(obs)
        self._sol    = self.findSol()

    def findSol(self):
        graph  = None
        sol    = None
        return sol
        
    def getSol(self):
        return self._sol

    def findGridPts(self, lr):
        pts = set()
        for (l, rects) in lr:
            layer = layers._mlayers[l] if l in layers._mlayers else None
            if layer and (layer._index <= layers._maxlayer._index) and (layer._index >= layers._minlayer._index):
                for other in [layers._index - 1, layers._index + 1]:
                    if other <= layers._maxlayer._index and other >= layers._minlayer._index:
                        ol = layers._mlarray[other]
                        for r in rects:
                            if layer._dir == 'H':
                                coords = ol._grid.getPointsInRange(r.xmin(), r.xmax())
                                for c in coords:
                                    pts.add((c, r.ycenter(), layer._index, other))
                            else:
                                coords = ol._grid.getPointsInRange(r.ymin(), r.ymax())
                                for c in coords:
                                    pts.add((r.xcenter(), c, layer._index, other))
                            
