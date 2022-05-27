#!/usr/bin/env python

import gdspy
import json
import argparse

class PRIMJSON2GDS:
    def __init__(self, layerfile, jsonfile):
        (self._layers, self._gdslayer) = self.readLayerInfo(layerfile)
        self._data = self.readJSON(jsonfile)
        self._scale = 1

    def readLayerInfo(self, layerfile):
        layers = dict()
        gdslayer = dict()
        with open(layerfile) as fp:
            layerdata = json.load(fp)
            if "ScaleFactor" in layerdata:
                self._scale = layerdata["ScaleFactor"]
            if "Abstraction" in layerdata:
                for l in layerdata["Abstraction"]:
                    if "Layer" in l and "GdsLayerNo" in l:
                        layer = l["Layer"]
                        gdslayer[layer] = l["GdsLayerNo"]
                        layers[layer] = dict()
                        if "GdsDatatype" in l:
                            layers[layer] = l["GdsDatatype"]
        return (layers, gdslayer)
    
    def readJSON(self, jsonfile):
        with open(jsonfile) as fp:
            return json.load(fp)
    
    def writeGDS(self, gdsfile):
        lib = gdspy.GdsLibrary(unit=1e-9)
        cell = lib.new_cell(gdsfile[0:gdsfile.rfind('.gds')])
        bboxlayer = self._gdslayer['Bbox'] if 'Bbox' in self._gdslayer \
                    else (self._gdslayer['Outline'] if 'Outline' in self._gdslayer else None)
        if ("bbox" in self._data and bboxlayer):
            bbox = [k/self._scale for k in self._data['bbox']]
            draw = self._layers['Outline']['Draw'] if 'Draw' in self._layers['Outline'] else 0
            cell.add(gdspy.Rectangle((bbox[0], bbox[1]), (bbox[2], bbox[3]), layer = bboxlayer, datatype = draw))
        if "terminals" in self._data:
            for t in self._data["terminals"]:
                layer = t["layer"] if "layer" in t else None
                rect  = [k / self._scale for k in t["rect"]] if "rect" in t else None
                nt    = t["netType"] if "netType" in t else 'Draw'
                nn    = t["netName"] if "netName" in t else None
                if layer and rect and layer in self._gdslayer:
                    if nt == 'pin':
                        nt = 'Pin'
                    elif nt == 'drawing':
                        nt = 'Draw'
                    draw = self._layers[layer][nt] if nt in self._layers[layer] else (self._layers['Draw'] if 'Draw' in self._layers else 0)
                    cell.add(gdspy.Rectangle((rect[0], rect[1]), (rect[2], rect[3]), layer = self._gdslayer[layer], datatype = draw))
                    if nn and 'Label' in self._layers[layer]:
                        cell.add(gdspy.Label(nn, ((rect[0] + rect[2])/2, (rect[1] + rect[3])/2), magnification = 4, \
                              layer = self._gdslayer[layer], texttype = self._layers[layer]['Label']))
                
        lib.write_gds(gdsfile)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument( "-j", "--json",    type=str, default="", help='<input.json file>')
    ap.add_argument( "-l", "--layers", type=str, default="", help='<layers.json file>')
    ap.add_argument( "-o", "--out", type=str, default="", help="<output filename>")
    args = ap.parse_args()
    
    if args.layers == "" or args.json == "":
        ap.print_help()
        exit(0)
    else:
        if args.out == "":
            args.out = args.json[0:args.json.rfind(".json")] + ".gds"
        print(f"json file    : {args.json}")
        print(f"layers       : {args.layers}")
        j2g = PRIMJSON2GDS(args.layers, args.json)
        print(f"writing out gds file : {args.out}")
        j2g.writeGDS(args.out)
