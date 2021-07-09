from collections import OrderedDict


class Wire:
    def __init__(self):
        self.netName = None
        self.rect = None
        self.layer = None
        self.gid = None
        self.color = None

    def __str__(self):
        return "Wire  net=%s%s layer=%s rect=%s" % (self.netName, ("" if self.gid is None else (
            " gid=%d" % self.gid)), self.layer, self.rect.toColonSepStr())

    def __repr__(self):
        return f"Wire(netName={self.netName}, rect={self.rect}, layer={self.layer}, gid={self.gid}, color={self.color}"

    def encode(self):
        return {"netName": self.netName,
                "layer": self.layer,
                "gid": self.gid,
                "rect": self.rect.toList(),
                "color": self.color
                }


class GR:
    def __init__(self):
        self.netName = None
        self.rect = None
        self.layer = None
        self.width = None
        self.connected_pins = None

    def __repr__(self):
        return f"GR(netName={self.netName}, rect={self.rect}, layer={self.layer}, width={self.width}"

    def encode(self, tech):
        # Convert global route coords to physical coords
        if self.rect.llx == self.rect.urx and self.rect.lly == self.rect.ury:
            raise RuntimeError(f"{self} is a point.")
        if self.rect.llx == self.rect.urx:  # vertical wire
            xc = tech.pitchPoly * (tech.halfXGRGrid * 2 * self.rect.llx + tech.halfXGRGrid)
            llx = xc - self.width // 2
            urx = xc + self.width // 2
            lly = tech.pitchDG * (tech.halfYGRGrid * 2 * self.rect.lly + tech.halfYGRGrid)
            ury = tech.pitchDG * (tech.halfYGRGrid * 2 * self.rect.ury + tech.halfYGRGrid)
        elif self.rect.lly == self.rect.ury:  # horizontal wire
            yc = tech.pitchDG * (tech.halfYGRGrid * 2 * self.rect.lly + tech.halfYGRGrid)
            lly = yc - self.width // 2
            ury = yc + self.width // 2
            llx = tech.pitchPoly * (tech.halfXGRGrid * 2 * self.rect.llx + tech.halfXGRGrid)
            urx = tech.pitchPoly * (tech.halfXGRGrid * 2 * self.rect.urx + tech.halfXGRGrid)
        else:
            raise RuntimeError(f"{self} is not a horizontal or vertical line.")

        return {"netName": self.netName,
                "layer": self.layer,
                "width": self.width,
                "rect": [llx, lly, urx, ury]
                }


class Net:
    def __init__(self, nm):
        self.nm = nm
        self.wires = []
        self.grs = []
        self.ces = OrderedDict()

    def __repr__(self):
        return f"Net(nm={self.nm}, wires={self.wires}, grs={self.grs}, ces={self.ces})"


class Netlist:
    def __init__(self, nm, bbox):
        self.nm = nm
        self.bbox = bbox
        self.nets = OrderedDict()
        self.gidIndex = 0
        self.wire_cache = {}
        self.instances = {}

    def newWire(self, netName, r, ly, *, ceName=None):
        """The wire cache is used to make sure we don't generate gid's for two different occs of the same wire """
        cand = (netName, (r.llx, r.lly, r.urx, r.ury), ly)
        if cand not in self.wire_cache:
            w = Wire()
            w.netName = netName
            w.rect = r
            w.layer = ly
            w.gid = self.gidIndex
            self.gidIndex += 1

            if netName not in self.nets:
                self.nets[netName] = Net(netName)

            self.nets[netName].wires.append(w)
            self.wire_cache[cand] = w
        else:
            w = self.wire_cache[cand]

        if ceName is not None:
            if ceName not in self.nets[netName].ces:
                self.nets[netName].ces[ceName] = []

            self.nets[netName].ces[ceName].append(w)

        return w

    def newGR(self, netName, r, ly, w, *, connected_pins=None):
        gr = GR()

        gr.netName = netName
        gr.layer = ly
        gr.rect = r.canonical()
        gr.width = w
        gr.connected_pins = connected_pins

        if netName not in self.nets:
            self.nets[netName] = Net(netName)

        self.nets[netName].grs.append(gr)

        return gr
