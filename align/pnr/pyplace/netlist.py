import json
import geom
from logger import logger
from pnrmacro import parseLef
import pulp

class Net:
    def __init__(self, name = "", isglobal = False):
        self._name     = name
        self._isGlobal = isglobal
        self._pins     = set()

class Instance:
    def __init__(self, name = "", isleaf = True, master = ""):
        self._name   = name
        self._master = master
        self._isLeaf = isLeaf
        self._nets   = dict()


class SymmConstr:
    def __init__(self, pairs = list(), direction = ''):
        self._selfsym   = list()
        self._sympairs  = list()
        self._direction = direction
        for p in pairs:
            if len(p) == 1:
                self._selfsym.append(p[0])
            elif len(p) == 2:
                self._sympairs.append((p[0], p[1]))


class OrderConstr:
    def __init__(self, instances = list(), direction = '', abut = False):
        self._instances = instances
        self._direction = direction
        self._abut      = abut


class AlignConstr:
    def __init__(self, instances = list(), line = ''):
        self._instances = instances
        self._line      = line


class SameTemplateConstr:
    def __init__(self, instances = list()):
        self._instances = instances


class Constr:
    def __init__(self):
        self._symm     = list()
        self._symm     = list()
        self._order    = list()
        self._align    = list()
        self._sametmpl = list()
        self._hdist    = 0
        self._vdist    = 0
        self._power    = list()
        self._ground   = list()
        self._clk      = list()

    def loadConstr(self, constraints):
        for c in constraints:
            ctype = c.get("constraint")
            if ctype:
                if ctype == "power_ports":
                    for p in c["ports"]:
                        self._power.append(p)
                elif ctype == "ground_ports":
                    for p in c["ports"]:
                        self._ground.append(p)
                elif ctype == "clock_ports":
                    for p in c["ports"]:
                        self._clk.append(p)
                elif ctype == "horizontal_distance":
                    self._hdist = c["abs_distance"]
                elif ctype == "vertical_distance":
                    self._vdist = c["abs_distance"]
                elif ctype == "symmetric_blocks":
                    self._symm.append(SymmConstr(c["pairs"], c["direction"]))
                elif ctype == "order":
                    self._order.append(OrderConstr(c["instances"], c["direction"], c["abut"]))
                elif ctype == "align":
                    self._align.append(AlignConstr(c["instances"], c["line"]))
                elif ctype == "same_template":
                    self._sametmpl.append(AlignConstr(c["instances"]))
                        
    def __repr__(self):
        return " sym : " + str(len(self._symm)) + " order : " + str(len(self._order)) \
            + " align : " + str(len(self._align)) + " sametmpl : " + str(len(self._sametmpl))

class Module:
    class Variant:
        def __init__(self):
            self._coords = dict()
            self._bbox   = Rect()
            self._netbox = dict()

    def __init__(self, name = "", params = list(), depth = -1):
        self._name      = name
        self._ports     = params
        self._depth     = depth
        self._nets      = dict()
        self._instances = dict()
        self._constr    = Constr()
        self._variants  = list()
        self._placed    = False

    def __repr__(self):
        return self._name + ' ' + repr(self._ports) + repr(self._constr)

    def loadInstance(self, inst):
        iname = inst.get("instance_name")
        if iname:
            self._instances[iname] = (inst["abstract_template_name"], None)
        for fa in inst["fa_map"]:
            faa = fa.get("actual")
            if faa not in self._nets:
                self._nets[faa] = [(inst["instance_name"],fa["formal"])]
            else:
                self._nets[faa].append((inst["instance_name"],fa["formal"]))

    def placeUsingILP(self):
        return None

    def place(self, N = 1):
        if not self._placed:
            for k, i in self._instances.items():
                if i[1] and not i[1]._placed:
                        i[1].place(N)
            self._placed = True
            self._variants = self.placeUsingILP()
            logger.info(f'placed {self._name}')


class Netlist:
    def __init__(self):
        self._modules        = dict()
        self._global_signals = set()
        self._macro_map      = dict()
        self._depth_list     = list()
        self._macros         = dict()
        self._topmodule      = None

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

    def build(self):
        for j, m in self._modules.items():
            for k, i in m._instances.items():
                mod = self._modules.get(i[0])
                if mod:
                    m._instances[k] = (i[0], mod)

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
                    self._depth_list.append(list())
            self._depth_list[m._depth].append(m)
        if len(self._depth_list) and self._depth_list[-1]:
            self._topmodule = self._depth_list[-1][0]

    def loadData(self, verilogFile = "", mapFile = "", lefFile = ""):
        self._macros = parseLef(lefFile)
        if verilogFile != "":
            with open(verilogFile) as fp:
                ver = json.load(fp)
                for m in ver.get("modules"):
                    modu = Module(m["name"], m["parameters"])
                    modu._constr.loadConstr(m.get("constraints"))
                    for inst in m.get("instances"):
                        modu.loadInstance(inst)
                    self._modules[modu._name] = modu
                for signal in ver.get("global_signals"):
                    act = signal.get("actual")
                    if act:
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
                        m = self._macros.get(var)
                        if m:
                            if sp[0] in self._macro_map:
                                self._macro_map[sp[0]].append(m)
                            else:
                                self._macro_map[sp[0]] = [m]
        self.build()

    def place(self, N = 1):
        if self._topmodule:
            self._topmodule.place(N)

