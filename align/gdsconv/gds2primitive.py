#!/usr/bin/env python

import json
import argparse
import os
import shutil
import copy

from .gds2lefjson import GDS2_LEF_JSON

class GEN_PRIMITIVE_FROM_GDS:
    def __init__(self, gdsdir, layers, primdir, topodir):
        if gdsdir == "" or layers == "" or primdir == "" or topodir == "":
            return
        if topodir[-1] != '/':
           topodir += '/'
        if primdir[-1] != '/':
           primdir += '/'
        if gdsdir[-1] != '/':
           gdsdir += '/'
        self._removedmodules = self.update_verilog_json(topodir)
        self.update_primitives_lib_json(topodir)
        if not self.update_primitives_json(primdir) or not self.add_primitive_files(gdsdir, layers, primdir):
            return

    def update_verilog_json(self, topodir):
        removedmodules = []
        for vjson in os.listdir(topodir):
            if vjson.endswith(".verilog.json"): 
                with open(topodir + vjson) as fp:
                    vjdata = json.load(fp)
                    fp.close()
                    toremove = []
                    if "modules" in vjdata:
                        for m in vjdata["modules"]:
                            if "instances" in m and len(m["instances"]) == 0 and "constraints" in m:
                                for c in m["constraints"]:
                                    if "is_digital" in c and c["is_digital"]:
                                        toremove.append(m)
                                        removedmodules.append([m["name"], m["parameters"]])
                                        break
                    for m in toremove:
                        vjdata["modules"].remove(m)
                    if len(toremove):
                        shutil.copy(topodir + vjson, topodir + vjson + '.bkp')
                        with open(topodir + vjson, 'wt') as ofp:
                            json.dump(vjdata, ofp, indent = 2)
                        toremove = []
        return removedmodules

    def update_primitives_lib_json(self, topodir): ## redundant for now
        for primlib in os.listdir(topodir):
            if primlib == "__primitives_library__.json":
                with open(topodir + primlib) as fp:
                    pdata = json.load(fp)
                    fp.close()
                    for m in self._removedmodules:
                        if len(m) == 2: pdata.append({"name":m[0], "pins":m[1]})
                if len(self._removedmodules):
                    shutil.copy(topodir + primlib, topodir + primlib + '.bkp')
                    with open(topodir + primlib, 'wt') as ofp:
                        json.dump(pdata, ofp, indent = 2)
                break
        
    def update_primitives_json(self, primdir):
        primjson = primdir + '__primitives__.json'
        if os.path.isfile(primjson):
            with open(primjson) as fp:
                pdata = json.load(fp)
                fp.close()
                if not len(pdata): pdata = dict()
                for m in self._removedmodules:
                    if len(m) == 2: pdata[m[0]] = {"abstract_template_name": m[0], "concrete_template_name": m[0]}
                if len(self._removedmodules):
                    shutil.copy(primjson, primjson + '.bkp')
                    with open(primjson, 'wt') as ofp:
                        json.dump(pdata, ofp, indent = 2)
        else:
            print(f'{primjson} not found')
            return False
        return True
        
    def add_primitive_files(self, gdsdir, layers, primdir):
        for m in self._removedmodules:
            gdsfile = gdsdir + m[0] + '.gds'
            if os.path.isfile(gdsfile):
                gds2lef = GDS2_LEF_JSON(layers, gdsfile, m[0])
                gds2lef.writeLEFJSON(primdir)
            else:
                gdsfile = gdsdir + m[0].lower() + '.gds'
                if os.path.isfile(gdsfile):
                    gds2lef = GDS2_LEF_JSON(layers, gdsfile, m[0])
                    gds2lef.writeLEFJSON(primdir)
                else:
                      print(f'leaf {gdsfile} not found')
                      return False
        return True

