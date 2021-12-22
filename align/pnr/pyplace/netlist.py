import json
import geom
from logger import logger
from pnrmacro import Macros

class Net:
  def __init__(self, name = "", isglobal = False):
    self._name     = name
    self._isGlobal = isglobal
    self._pins     = set()

class Instance:
  def __init__(self, name = "", isleaf = True, master = ""):
    self._name = name
    self._master = master
    self._isLeaf = isLeaf
    self._nets = dict()


class Module:
  def __init__(self, name = "", params = [], depth = -1):
    self._name      = name
    self._ports     = params
    self._depth     = depth
    self._nets      = dict()
    self._instances = dict()
  def __repr__(self):
    return self._name

  def loadInstance(self, inst):
    if "instance_name" in inst:
      self._instances[inst["instance_name"]] = (inst["abstract_template_name"], None)
    for fa in inst["fa_map"]:
      if fa["actual"] not in self._nets:
        self._nets[fa["actual"]] = [(inst["instance_name"],fa["formal"])]
      else:
        self._nets[fa["actual"]].append((inst["instance_name"],fa["formal"]))
      
    
class Netlist:

  def __init__(self):
    self._modules = dict()
    self._global_signals = set()
    self._macro_map = dict()
    self._depth_list = [[]]
    self._macros = Macros()


  def print(self):
    for m, v in self._modules.items():
      logger.debug(f"module : {v._name}")
      logger.debug(f"\t\tports : {v._ports}")
      logger.debug(f"\t\tinstances : {v._instances}")
      logger.debug(f"\t\tnets : {v._nets}")
      logger.debug(f"\t\tdepth : {v._depth}")
    logger.debug(f'global signals : {self._global_signals}')
    logger.debug('map :')
    for m, v in self._macro_map.items():
      logger.debug(f'\t\t{m} : {v}')
    for k in range(len(self._depth_list)):
      logger.debug(f'\t\t{k} : {self._depth_list[k]}')

  def loadVerilogMap(self, verilogFile = "", mapFile = ""):
    if verilogFile != "":
      with open(verilogFile) as fp:
        ver = json.load(fp)
        if "modules" in ver:
          for m in ver["modules"]:
            modu = Module(m["name"], m["parameters"])
            if "instances" in m:
              for inst in m["instances"]:
                modu.loadInstance(inst)
            self._modules[modu._name] = modu
        if "global_signals" in ver:
          for signal in ver["global_signals"]:
            if "actual" in signal:
              self._global_signals.add(signal["actual"])
    if mapFile != "":
      with open(mapFile) as fp:
        lines = fp.readlines()
        for line in lines:
          line = line.strip()
          sp = line.split()
          if len(sp) >= 2:
            var = sp[1]
            poss = max(var.find("/"), 0)
            posp = var.find(".")
            if (posp >= 0):
              var = sp[1][poss:posp]
            if sp[0] in self._macro_map:
              self._macro_map[sp[0]].append(var)
            else:
              self._macro_map[sp[0]] = [var]


  def build(self, lefFile = ""):
    self._macros.parseLef(lefFile)
    for j, m in self._modules.items():
      for k, i in m._instances.items():
        if i[0] in self._modules:
          m._instances[k] = (i[0], self._modules[i[0]])

    def calcdepth(mod):
      maxdepth = -1
      for k, i in mod._instances.items():
        if i[1]:
          if i[1]._depth < 0:
            calcdepth(i[1])
          maxdepth = max(maxdepth, i[1]._depth)
        else:
          assert (i[0] in self._macro_map)
      mod._depth = maxdepth + 1
    for j, m in self._modules.items():
      calcdepth(m)

    for j, m in self._modules.items():
      if len(self._depth_list) < m._depth + 1:
        for k in range(len(self._depth_list), m._depth + 1):
          self._depth_list.append([])
      self._depth_list[m._depth].append(m)
