#!/usr/bin/env python3

import numpy
import gdstk
import json
import argparse
import os


class MetalLayer:
  def __init__(self, js):
    self._name = js["Layer"]
    self._width = js["Width"] * 1e-9
    self._pitch = js["Pitch"] * 1e-9
    self._offset = js["Offset"] * 1e-9
    self._vert = (js["Direction"] == "V")
    self._shapeGDS = (js["GdsLayerNo"], js["GdsDatatype"]["Draw"])
    self._labelGDS = js["LabelLayerNo"] if "LabelLayerNo" in js else (js["GdsLayerNo"], js["GdsDatatype"]["Label"])

  def __repr__(self):
    return f'metal : ({self._name}, {self._width}, {self._pitch}, GDS:{self._shapeGDS}, Label:{self._labelGDS})'

class ViaLayer:
  def __init__(self, js):
    self._name = js["Layer"]
    self._layer = js["Stack"]
    self._width = (js["WidthX"] * 1e-9, js["WidthY"] * 1e-9)
    self._spacing = (js["SpaceX"] * 1e-9, js["SpaceY"] * 1e-9)
    self._encl = (js["VencA_L"] * 1e-9, js["VencP_L"] * 1e-9)
    self._ench = (js["VencA_H"] * 1e-9, js["VencP_H"] * 1e-9)
    self._shapeGDS = (js["GdsLayerNo"], js["GdsDatatype"]["Draw"])
    self._labelGDS = js["LabelLayerNo"] if "LabelLayerNo" in js else None

  def __repr__(self):
    return f'metal : ({self._name}, {self._width}, {self._spacing}, GDS:{self._shapeGDS}, Label:{self._labelGDS})'

class PowerGridData:
  def __init__(self, jf, constr):
    self._mlayers = list()
    self._vlayers = dict()
    self._railFreq = 0
    js = dict()
    with open(jf, 'rt') as fp:
      js = json.load(fp)

    if "design_info" in js:
      di = js["design_info"]
      tl = int(di["top_power_grid_layer"][1:])
      bl = int(di["bottom_power_grid_layer"][1:])
      self._mlayerNames = [f'M{i}' for i in range(bl, tl+1)]
      self._vlayerNames = [f'V{i}' for i in range(bl, tl)]
      for layerit in js["Abstraction"]:
        if layerit["Layer"] in self._mlayerNames:
          self._mlayers.append(MetalLayer(layerit))
        if layerit["Layer"] in self._vlayerNames:
          self._vlayers[layerit["Layer"]] = ViaLayer(layerit)
      self._railFreq = di["power_rail_frequency"]

    self._mlMap = {l._shapeGDS:l for l in self._mlayers}

    
    cf = dict()
    if constr:
      with open(constr, 'rt') as fp:
        cf = json.load(fp)
    self._powernets = []
    for it in cf:
      if "constraint" in it and it["constraint"] in ("PowerPorts", "GroundPorts"):
        for net in it["ports"]:
          self._powernets.append(net)
    print(f"power nets : {self._powernets}")
        

  def mGDS(self):
    return set([l._shapeGDS for l in self._mlayers])

  def vGDS(self):
    return set([l._shapeGDS for l in self._vlayers.values()])


if __name__ == "__main__":
  ap = argparse.ArgumentParser()
  ap.add_argument( "-g", "--gds",    type=str,  default="", help='<top-level layout for which the power grid has to be inserted>')
  ap.add_argument( "-l", "--layers", type=str,  default="", help='<path to layers.json file>')
  ap.add_argument( "-c", "--constr", type=str,  default="", help='<constraints .const.json file>')
  ap.add_argument( "-o", "--out",    type=str,  default="", help='<output GDS file>')
  args = ap.parse_args()
  print(f"input GDS  : {args.gds}")
  print(f"layers     : {args.layers}")
  print(f"output GDS : {args.out}")
  if (args.gds):
    if not os.path.isfile(args.gds):
      print(f'{args.gds} not found')
      exit()
  
  gdslib = gdstk.read_gds(args.gds)
  topcell = gdslib.top_level()[0] if len(gdslib.top_level()) > 0 else None
  if topcell:
    topcell.flatten()
  bbox = topcell.bounding_box()

  p = PowerGridData(args.layers, args.constr)

  mlayers = p.mGDS()
  vlayers = p.vGDS()
  from collections import defaultdict
  layerPolygons = defaultdict(list)
  for pl in topcell.polygons:
    g = (pl.layer, pl.datatype)
    if g in mlayers or g in vlayers:
      layerPolygons[g].append(pl)

  pg = defaultdict(list)
# create potential grid shapes on all layers
  for m in p._mlayers:
    hw = m._width / 2
    v1 = "V" + str(int(m._name[1:]) - 1)
    v2 = "V" + m._name[1:]
    vlayer1 = p._vlayers[v2] if v2 in p._vlayers else None
    vlayer2 = p._vlayers[v1] if v1 in p._vlayers else None
# offset to accommodate via enclosure on both above/below layers
    viaoffset = vlayer1._encl[0] if vlayer1 else 0
    if vlayer2:
      viaoffset = max(viaoffset, vlayer2._ench[0])
    if m._vert:
      x = bbox[0][0] + m._offset + hw + viaoffset
      while x < (bbox[1][0] - hw):
        xmin, ymin, xmax, ymax = x - hw, bbox[0][1], x + hw, bbox[1][1]
        box = gdstk.rectangle([xmin * 1e6, ymin * 1e6], [xmax * 1e6, ymax * 1e6], layer=m._shapeGDS[0], datatype=m._shapeGDS[1])
        pg[m._shapeGDS].append(box)
        x += p._railFreq * m._pitch
    else:
      y = bbox[0][1] + m._offset + hw + viaoffset
      while y < (bbox[1][1] - hw):
        xmin, ymin, xmax, ymax = bbox[0][0], y - hw, bbox[1][0], y + hw
        box = gdstk.rectangle([xmin * 1e6, ymin * 1e6], [xmax * 1e6, ymax * 1e6], layer=m._shapeGDS[0], datatype=m._shapeGDS[1])
        pg[m._shapeGDS].append(box)
        y += p._railFreq * m._pitch
  
# Boolean NOT of potential grid shapes with existing obstacles
  pga = defaultdict(list)
  for k, v in pg.items():
    rects = []
    for r in layerPolygons[k]:
      b = r.bounding_box()
      rects.append(gdstk.rectangle([b[0][0]*1e6, b[0][1]*1e6], [b[1][0]*1e6, b[1][1]*1e6]))
    res = gdstk.boolean(v, rects, "not")
    for r in res:
      b = r.bounding_box()
# Only consider shapes that span the entire width or height of the bounding box
      if (b[0][0] == bbox[0][0]*1e6 and b[1][0] == bbox[1][0]*1e6) or (b[0][1] == bbox[0][1]*1e6 and b[1][1] == bbox[1][1]*1e6):
        r.layer=k[0]
        r.datatype=k[1]
        pga[k].append(r)

  netMap = [defaultdict(list) for i in range(len(p._powernets))]
  for k, v in pga.items():
    for i in range(len(v)):
      netMap[i % len(netMap)][k].append(v[i])

  def overlaps(lS, uS):
    bls = lS.bounding_box()
    uls = uS.bounding_box()
    if bls[0][0] < uls[1][0] and bls[1][0] > uls[0][0] and bls[0][1] < uls[1][1] and bls[1][1] > uls[0][1]:
      return ((max(bls[0][0], uls[0][0]) + min(bls[1][0], uls[1][0]))/2,\
          (max(bls[0][1], uls[0][1]) + min(bls[1][1], uls[1][1]))/2)
    return None

  layerMap = {l._name:l for l in p._mlayers}
  viaShapes = defaultdict(list)
  for nm in netMap:
    for k in nm:
      l1 = p._mlMap[k]
      l2name = "M" + str(int(l1._name[1:]) + 1)
      l2 = layerMap[l2name] if l2name in layerMap else None
      if l2:
        k2 = l2._shapeGDS
        v1 = p._vlayers["V" + l1._name[1:]]
        vl  = v1._shapeGDS
        hwx = v1._width[0] * 1e6/2
        hwy = v1._width[1] * 1e6/2
        for lS in nm[k]:
          for uS in nm[k2]:
            ol = overlaps(lS, uS)
            if None != ol:
              rect = gdstk.rectangle((ol[0] - hwx, ol[1] - hwy), (ol[0] + hwx, ol[1] + hwy), layer = vl[0], datatype = vl[1])
              viaShapes[vl].append(rect)
        

  og = gdstk.Library()
  tc = gdstk.Cell('PG')
# add power grid and boundary to the output stream
  tc.add(gdstk.rectangle([bbox[0][0]*1e6, bbox[0][1]*1e6], [bbox[1][0]*1e6, bbox[1][1]*1e6], layer=100 , datatype=0))
  for k, v in pga.items():
    for q in v:
      tc.add(q)
  for k, v in viaShapes.items():
    for q in v:
      tc.add(q)
  og.add(tc)
  for i in range(len(p._powernets)):
    net = p._powernets[i]
    shapeMap = netMap[i]
    for k, v in shapeMap.items():
      gd = p._mlMap[k]._labelGDS
      for s in v:
        b = s.bounding_box()
        c = ((b[0][0] + b[1][0])/2, (b[0][1] + b[1][1])/2)
        tc.add(gdstk.Label(net, c, layer = gd[0], texttype=gd[1]))

  print(f"Writing power grid to file: {args.out}")
  writer = gdstk.GdsWriter(args.out)
  writer.write(tc)
  writer.close()
