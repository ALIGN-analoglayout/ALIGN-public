import json

class point:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class bbox:
    def __init__(self, d):    
        self._d = d
        self.polygon = [ point(x) for x in d["polygon"]]
        self.LL = point(d["LL"])
        self.LR = point(d["LR"])
        self.UL = point(d["UL"])
        self.UR = point(d["UR"])

    def __getattr__(self, nm):
        return self._d[nm]


class block:
    def __init__(self, d):    
        self._d = d
        self.originBox = bbox(d["originBox"])
        self.originCenter = point(d["originCenter"])
        self.placedBox = bbox(d["placedBox"])
        self.placedCenter = point(d["placedCenter"])
        self.blockPins = [ pin(x) for x in d["blockPins"]]
        self.interMetals = [ contact(x) for x in d["interMetals"]]
        self.interVias = [ Via(x) for x in d["interVias"]]
        self.dummy_power_pin = [ pin(x) for x in d["dummy_power_pin"]]

    def __getattr__(self, nm):
        return self._d[nm]

class blockComplex:
    def __init__(self, d):    
        self._d = d
        self.instance = [ block(x) for x in d["instance"]]

    def __getattr__(self, nm):
        return self._d[nm]

class Metal:
    def __init__(self, d):
        self._d = d
        self.LinePoint = [ point(x) for x in d["LinePoint"]]
        self.MetalRect = contact(d["MetalRect"])

    def __getattr__(self, nm):
        return self._d[nm]

class Via:
    def __init__(self, d):    
        self._d = d
        self.originpos = point(d["originpos"])
        self.placedpos = point(d["placedpos"])
        self.UpperMetalRect = contact(d["UpperMetalRect"])
        self.LowerMetalRect = contact(d["LowerMetalRect"])
        self.ViaRect = contact(d["ViaRect"])

    def __getattr__(self, nm):
        return self._d[nm]


class net:
    def __init__(self, d):    
        self._d = d
        self.connected = [ connectNode(x) for x in d["connected"]]
        self.segments = [ contact(x) for x in d["segments"]]
        self.interVias = [ contact(x) for x in d["interVias"]]
        self.path_metal = [ Metal(x) for x in d["path_metal"]]
        self.path_via = [ Via(x) for x in d["path_via"]]
        self.connectedContact = [ globalContact(x) for x in d["connectedContact"]]

    def __getattr__(self, nm):
        return self._d[nm]

class terminal:
    def __init__(self, d):    
        self._d = d
        self.termContacts = [ contact(x) for x in d["termContacts"]]

    def __getattr__(self, nm):
        return self._d[nm]

class PowerGrid:
    def __init__(self, d):    
        self._d = d
        self.metals = [ Metal(x) for x in d["metals"]]
        self.vias = [ Via(x) for x in d["vias"]]


    def __getattr__(self, nm):
        return self._d[nm]

class PowerNet:
    def __init__(self, d):    
        self._d = d
        self.Pins = [ pin(x) for x in d["Pins"]]
        self.connected = [ connectNode(x) for x in d["Pins"]]
        self.dummy_connected = [ connectNode(x) for x in d["Pins"]]
        self.path_metal = [ Metal(x) for x in d["path_metal"]]
        self.path_via = [ Via(x) for x in d["path_via"]]

    def __getattr__(self, nm):
        return self._d[nm]

class pin:
    def __init__(self, d):    
        self._d = d
        self.pinContacts = [ contact(x) for x in d["pinContacts"]]
        self.pinVias = [ Via(x) for x in d["pinVias"]]

    def __getattr__(self, nm):
        return self._d[nm]

class contact:
    def __init__(self, d):    
        self._d = d
        self.originBox = bbox(d["originBox"])
        self.placedBox = bbox(d["placedBox"])
        self.originCenter = point(d["originCenter"])
        self.placedCenter = point(d["placedCenter"])

    def __getattr__(self, nm):
        return self._d[nm]

class globalContact:
    def __init__(self, d):    
        self._d = d
        self.conTact = contact(d["conTact"])

    def __getattr__(self, nm):
        return self._d[nm]

class connectNode:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class layoutAS:
    def __init__(self, d):    
        self._d = d
        self.Blocks = [ blockComplex(x) for x in d["Blocks"]]
        self.Nets = [ net(x) for x in d["Nets"]]
        self.Terminals = [ terminal(x) for x in d["Terminals"]]        

    def __getattr__(self, nm):
        return self._d[nm]

class SymmNet:
    def __init__(self, d):    
        self._d = d
        self.net1 = net(d["net1"])
        self.net2 = net(d["net2"])

    def __getattr__(self, nm):
        return self._d[nm]

class SymmPairBlock:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class Preplace:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class Alignment:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class Abument:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class MatchBlock:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class PortPos:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class AlignBlock:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class CCCap:
    def __init__(self, d):    
        self._d = d

    def __getattr__(self, nm):
        return self._d[nm]

class hierNode:
    def __init__(self, d):
        self._d = d
        self.Blocks = [ blockComplex(x) for x in d["Blocks"]]
        self.Nets = [ net(x) for x in d["Nets"]]
        self.Terminals = [ terminal(x) for x in d["Terminals"]]
        self.Vdd = PowerGrid(d["Vdd"])
        self.Gnd = PowerGrid(d["Gnd"])
        self.PowerNets = [ PowerNet(x) for x in d["PowerNets"]]
        self.blockPins = [ pin(x) for x in d["blockPins"]]
        self.interMetals = [ contact(x) for x in d["interMetals"]]
        self.interVias = [ Via(x) for x in d["interVias"]]
        self.PnRAS = [ layoutAS(x) for x in d["PnRAS"]]

        self.SNets = [ SymmNet(x) for x in d["SNets"]]
        self.SPBlocks = [ SymmPairBlock(x) for x in d["SPBlocks"]]
        self.Preplace_blocks = [ Preplace(x) for x in d["Preplace_blocks"]]
        self.Alignment_blocks = [ Alignment(x) for x in d["Alignment_blocks"]]
        self.Align_blocks = [ AlignBlock(x) for x in d["Align_blocks"]]
        self.Abument_blocks = [ Abument(x) for x in d["Abument_blocks"]]
        self.Match_blocks = [ MatchBlock(x) for x in d["Match_blocks"]]
        self.CC_Caps = [ CCCap(x) for x in d["CC_Caps"]]
        self.Port_Location = [ PortPos(x) for x in d["Port_Location"]]

    def __getattr__(self, nm):
        return self._d[nm]

structs = [(hierNode,[("isCompleted",None),
                      ("isTop",None),
                      ("width",None),
                      ("height",None),
                      ("name",None),
                      ("gdsFile",None),
                      ("parent",(list,None)),
                      ("Blocks", (list, blockComplex)),
                      ("Nets", (list, net)),
                      ("Terminals", (list, terminal)),
                      ("Vdd", PowerGrid),
                      ("Gnd", PowerGrid),
                      ("PowerNets", (list,PowerNet)),
                      ("blockPins", (list,pin)),
                      ("interMetals", (list,contact)),
                      ("interVias", (list,Via)),
                      ("PnRAS", (list,layoutAS)),
                      ("SNets", (list,SymmNet)),
                      ("SPBlocks", (list,SymmPairBlock)),
                      ("Preplace_blocks", (list,Preplace)),
                      ("Alignment_blocks", (list,Alignment)),
                      ("Align_blocks", (list,AlignBlock)),
                      ("Abument_blocks", (list,Abument)),
                      ("Match_blocks", (list,MatchBlock)),
                      ("CC_Caps", (list,CCCap)),
                      ("Port_Location", (list,PortPos)),
                      ("bias_Hgraph",None),
                      ("bias_Vgraph",None)
           ]),
           (blockComplex,[("instance",(list, block)),
                          ("selectedInstance",None),
                          ("child",None),
                          ("instNum",None)
           ]),
           (block,[("name",None),
                   ("master",None),
                   ("lefmaster",None),
                   ("type",None),
                   ("width",None),
                   ("height",None),
                   ("isLeaf",None),
                   ("originBox",bbox),
                   ("originCenter",point),
                   ("gdsFile",None),
                   ("orient",None),
                   ("placedBox",bbox),
                   ("placedCenter",point),
                   ("blockPins",(list,pin)),
                   ("interMetals",(list,contact)),
                   ("interVias",(list,Via)),
                   ("dummy_power_pin",(list,pin)),
           ]),
           (terminal,[("name",None),
                      ("type",None),
                      ("netIter",None),
                      ("termContacts",(list,contact))
           ]),
           (bbox,[("polygon",(list, point)),
                  ("LL",point),
                  ("LR",point),
                  ("UL",point),
                  ("UR",point)
           ]),
           (point,[("x",None),
                   ("y",None)
           ]),
           (contact,[("metal",None),
                     ("originBox",bbox),
                     ("placedBox",bbox),
                     ("originCenter",point),
                     ("placedCenter",point)
           ]),
           (connectNode,[("type",None),
                         ("iter",None),
                         ("iter2",None)
           ]),
           (globalContact,[("conTact",contact),
                           ("MetalIdx",None)
           ]),
           (net,[("name",None),
                 ("shielding",None),
                 ("sink2Terminal",None),
                 ("degree",None),
                 ("symCounterpart",None),
                 ("iter2SNetLsit",None),
                 ("connected",(list, connectNode)),
                 ("priority",None),
                 ("segments",(list,contact)),
                 ("interVias",(list,contact)),
                 ("path_metal",(list,Metal)),
                 ("path_via",(list,Via)),
                 ("connectedContact",(list,globalContact)),
                 ("axis_dir",None),
                 ("axis_coor",None)
           ]),
           (Metal,[("MetalIdx",None),
                   ("LinePoint",(list,point)),
                   ("width",None),
                   ("MetalRect",contact)
           ]),
           (Via,[("model_index",None),
                 ("originpos",point),
                 ("placedpos",point),
                 ("UpperMetalRect",contact),
                 ("UpperMetalRect",contact),
                 ("LowerMetalRect",contact),
                 ("ViaRect",contact)
           ]),
           (pin,[("name",None),
                 ("type",None),
                 ("use",None),
                 ("netIter",None),
                 ("pinContacts",(list,contact)),
                 ("pinVias",(list,Via)),
           ]),
           (PowerGrid,[("metals",(list,Metal)),
                       ("vias",(list,Via)),
                       ("power",None)
           ]),
           (PowerNet,[("name",None),
                      ("power",None),
                      ("Pins",(list,pin)),
                      ("connected",(list,connectNode)),
                      ("dummy_connected",(list,connectNode)),
                      ("path_metal",(list,Metal)),
                      ("path_via",(list,Via)),
           ]),
           (layoutAS,[("width",None),
                      ("height",None),
                      ("gdsFile",None),
                      ("Blocks",(list,blockComplex)),
                      ("Nets",(list,net)),
                      ("Terminals",(list,terminal))
           ]),
           (SymmNet,[("net1",net),
                     ("net2",net),
                     ("iter1",None),
                     ("iter2",None)
           ]),
           (SymmPairBlock,[("sympair",(list,None)),
                           ("selfsym",(list,None))
           ]),
           (Preplace,[("blockid1",None),
                      ("blockid2",None),
                      ("conner",None),
                      ("distance",None),
                      ("horizon",None)
           ]),
           (Alignment,[("blockid1",None),
                       ("blockid2",None),
                       ("distance",None),
                       ("horizon",None)
           ]),
           (Abument,[("blockid1",None),
                     ("blockid2",None),
                     ("distance",None),
                     ("horizon",None)
           ]),
           (MatchBlock,[("blockid1",None),
                        ("blockid2",None)
           ]),
           (AlignBlock,[("blocks",(list,None)),
                        ("horizon",None)
           ]),
           (PortPos,[("tid",None),
                     ("pos",None)
           ]),
           (CCCap,[("size",(list,None)),
                   ("CCCap_name",None),
                   ("Unit_capacitor",None),
                   ("cap_ratio",None),
                   ("cap_r",None),
                   ("cap_s",None)
           ]),
]

class PnRDBEncoder(json.JSONEncoder):
    def default(self, obj):
        def f(x,v):
            assert v is None or isinstance( x, v)
            return x if v is None else self.default(x)

        for (klass,fields) in structs:
            if isinstance(obj, klass):
                return {k : ( [f(x,v[1]) for x in a] if isinstance( v, tuple) and v[0] is list else f(a,v)) for (k,v) in fields for a in (getattr(obj,k),)}

        return json.JSONEncoder.default(self, obj)

def test_A():
    with open("../telescopic_ota-freeze.json","rt") as fp:
        j = json.load(fp)
        hN = hierNode(j)

    with open("__json","wt") as fp:
        json.dump( hN, fp=fp, cls=PnRDBEncoder, indent=2)

    with open("__json2","wt") as fp:
        json.dump( j, fp=fp, indent=2)

    with open("__json","rt") as fp:
        jj = json.load(fp)

    assert j == jj

