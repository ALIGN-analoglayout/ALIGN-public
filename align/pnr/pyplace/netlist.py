import json
import geom
from logger import logger

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
    self._name = name
    self._ports = params
    self._depth = depth
    self._nets = dict()
    self._instances = dict()

  def loadInstance(self, inst):
    if "instance_name" in inst:
      self._instances[inst["instance_name"]] = inst["abstract_template_name"]
    for fa in inst["fa_map"]:
      if fa["actual"] not in self._nets:
        self._nets[fa["actual"]] = [(inst["instance_name"],fa["formal"])]
      else:
        self._nets[fa["actual"]].append((inst["instance_name"],fa["formal"]))
      
    
class Netlist:

  def __init__(self):
    self._modules = dict()
    self._global_signals = set()

  def print(self):
    for m, v in self._modules.items():
      logger.debug(f"module : {v._name} {v._ports} {v._instances} {v._nets}")
    logger.debug(f'global signals : {self._global_signals}')

  def loadVerilog(self, verilogFile = ""):
    if verilogFile == "":
      return
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
        

