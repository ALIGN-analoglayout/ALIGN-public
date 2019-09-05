import json

abstract_structs = [
           ("point",[("x",None),
                   ("y",None)
           ]),
           ("bbox",[("polygon",(list, "point")),
                  ("LL","point"),
                  ("LR","point"),
                  ("UL","point"),
                  ("UR","point")
           ]),
           ("contact",[("metal",None),
                     ("originBox","bbox"),
                     ("placedBox","bbox"),
                     ("originCenter","point"),
                     ("placedCenter","point")
           ]),
           ("terminal",[("name",None),
                      ("type",None),
                      ("netIter",None),
                      ("termContacts",(list,"contact"))
           ]),
           ("connectNode",[("type",None),
                         ("iter",None),
                         ("iter2",None)
           ]),
           ("globalContact",[("conTact","contact"),
                           ("MetalIdx",None)
           ]),
           ("net",[("name",None),
                 ("shielding",None),
                 ("sink2Terminal",None),
                 ("degree",None),
                 ("symCounterpart",None),
                 ("iter2SNetLsit",None),
                 ("connected",(list, "connectNode")),
                 ("priority",None),
                 ("segments",(list,"contact")),
                 ("interVias",(list,"contact")),
                 ("path_metal",(list,"Metal")),
                 ("path_via",(list,"Via")),
                 ("connectedContact",(list,"globalContact")),
                 ("axis_dir",None),
                 ("axis_coor",None)
           ]),
           ("SymmNet",[("net1","net"),
                     ("net2","net"),
                     ("iter1",None),
                     ("iter2",None)
           ]),
           ("SymmPairBlock",[("sympair",(list,None)),
                           ("selfsym",(list,None))
           ]),
           ("Preplace",[("blockid1",None),
                      ("blockid2",None),
                      ("conner",None),
                      ("distance",None),
                      ("horizon",None)
           ]),
           ("Alignment",[("blockid1",None),
                       ("blockid2",None),
                       ("distance",None),
                       ("horizon",None)
           ]),
           ("Abument",[("blockid1",None),
                     ("blockid2",None),
                     ("distance",None),
                     ("horizon",None)
           ]),
           ("MatchBlock",[("blockid1",None),
                        ("blockid2",None)
           ]),
           ("AlignBlock",[("blocks",(list,None)),
                        ("horizon",None)
           ]),
           ("PortPos",[("tid",None),
                     ("pos",None)
           ]),
           ("CCCap",[("size",(list,None)),
                   ("CCCap_name",None),
                   ("Unit_capacitor",None),
                   ("cap_ratio",None),
                   ("cap_r",None),
                   ("cap_s",None)
           ]),
           ("Metal",[("MetalIdx",None),
                   ("LinePoint",(list,"point")),
                   ("width",None),
                   ("MetalRect","contact")
           ]),
           ("Via",[("model_index",None),
                 ("originpos","point"),
                 ("placedpos","point"),
                 ("UpperMetalRect","contact"),
                 ("LowerMetalRect","contact"),
                 ("ViaRect","contact")
           ]),
           ("pin",[("name",None),
                 ("type",None),
                 ("use",None),
                 ("netIter",None),
                 ("pinContacts",(list,"contact")),
                 ("pinVias",(list,"Via")),
           ]),


           ("block",[("name",None),
                   ("master",None),
                   ("lefmaster",None),
                   ("type",None),
                   ("width",None),
                   ("height",None),
                   ("isLeaf",None),
                   ("originBox","bbox"),
                   ("originCenter","point"),
                   ("gdsFile",None),
                   ("orient",None),
                   ("placedBox","bbox"),
                   ("placedCenter","point"),
                   ("blockPins",(list,"pin")),
                   ("interMetals",(list,"contact")),
                   ("interVias",(list,"Via")),
                   ("dummy_power_pin",(list,"pin")),
           ]),
           ("blockComplex",[("instance",(list, "block")),
                          ("selectedInstance",None),
                          ("child",None),
                          ("instNum",None)
           ]),
           ("PowerGrid",[("metals",(list,"Metal")),
                       ("vias",(list,"Via")),
                       ("power",None)
           ]),
           ("PowerNet",[("name",None),
                      ("power",None),
                      ("Pins",(list,"pin")),
                      ("connected",(list,"connectNode")),
                      ("dummy_connected",(list,"connectNode")),
                      ("path_metal",(list,"Metal")),
                      ("path_via",(list,"Via")),
           ]),
           ("layoutAS",[("width",None),
                      ("height",None),
                      ("gdsFile",None),
                      ("Blocks",(list,"blockComplex")),
                      ("Nets",(list,"net")),
                      ("Terminals",(list,"terminal"))
           ]),

          ("hierNode",[("isCompleted",None),
                      ("isTop",None),
                      ("width",None),
                      ("height",None),
                      ("name",None),
                      ("gdsFile",None),
                      ("parent",(list,None)),
                      ("Blocks", (list, "blockComplex")),
                      ("Nets", (list, "net")),
                      ("Terminals", (list, "terminal")),
                      ("Vdd", "PowerGrid"),
                      ("Gnd", "PowerGrid"),
                      ("PowerNets", (list,"PowerNet")),
                      ("blockPins", (list,"pin")),
                      ("interMetals", (list,"contact")),
                      ("interVias", (list,"Via")),
                      ("PnRAS", (list,"layoutAS")),
                      ("SNets", (list,"SymmNet")),
                      ("SPBlocks", (list,"SymmPairBlock")),
                      ("Preplace_blocks", (list,"Preplace")),
                      ("Alignment_blocks", (list,"Alignment")),
                      ("Align_blocks", (list,"AlignBlock")),
                      ("Abument_blocks", (list,"Abument")),
                      ("Match_blocks", (list,"MatchBlock")),
                      ("CC_Caps", (list,"CCCap")),
                      ("Port_Location", (list,"PortPos")),
                      ("bias_Hgraph",None),
                      ("bias_Vgraph",None)
           ])
]


class FallbackJSON:
    def __init__(self, d):    
        self.__dict__['_d'] = d

    def __getattr__(self, nm):
        return self._d[nm]

    def __setattr__(self, nm, v):
        self._d[nm] = v

for (k,v) in abstract_structs:
    attrs_dict = {}
    for (nm,vv) in v:
        def init_fn(self, d):
            FallbackJSON.__init__(self, d)
            if isinstance( vv, tuple):
                assert vv[0] is list
                if vv[1] is None:
                    self.__dict__[nm] = [ x for x in d[nm]]
                else:
                    klass = globals()[vv[1]]
                    self__dict__[nm] = [ klass(x) for x in d[nm]]
            else:
                if vv is None:
                    if nm in d:
#
# Runs 5x slower if you include this
# Not doing it means you need to keep the JSON shadow around
#                        self.__dict__[nm] = d[nm]
                        pass
                    else:
#                        print("Missing field for", nm, k, "in JSON")
                        pass
                else:
                    klass = globals()[vv]
                    self__dict__[nm] = klass(x)
        attrs_dict["__init__"] = init_fn
    print( k,v, attrs_dict)
    globals()[k] = type( k, (FallbackJSON,), attrs_dict)

class block(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['originBox'] = bbox(d["originBox"])
        self.__dict__['originCenter'] = point(d["originCenter"])
        self.__dict__['placedBox'] = bbox(d["placedBox"])
        self.__dict__['placedCenter'] = point(d["placedCenter"])
        self.__dict__['blockPins'] = [ pin(x) for x in d["blockPins"]]
        self.__dict__['interMetals'] = [ contact(x) for x in d["interMetals"]]
        self.__dict__['interVias'] = [ Via(x) for x in d["interVias"]]
        self.__dict__['dummy_power_pin'] = [ pin(x) for x in d["dummy_power_pin"]]

class blockComplex(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['instance'] = [ block(x) for x in d["instance"]]

class Metal(FallbackJSON):
    def __init__(self, d):
        super().__init__(d)
        self.__dict__['LinePoint'] = [ point(x) for x in d["LinePoint"]]
        self.__dict__['MetalRect'] = contact(d["MetalRect"])

class Via(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['originpos'] = point(d["originpos"])
        self.__dict__['placedpos'] = point(d["placedpos"])
        self.__dict__['UpperMetalRect'] = contact(d["UpperMetalRect"])
        self.__dict__['LowerMetalRect'] = contact(d["LowerMetalRect"])
        self.__dict__['ViaRect'] = contact(d["ViaRect"])

class net(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['connected'] = [ connectNode(x) for x in d["connected"]]
        self.__dict__['segments'] = [ contact(x) for x in d["segments"]]
        self.__dict__['interVias'] = [ contact(x) for x in d["interVias"]]
        self.__dict__['path_metal'] = [ Metal(x) for x in d["path_metal"]]
        self.__dict__['path_via'] = [ Via(x) for x in d["path_via"]]
        self.__dict__['connectedContact'] = [ globalContact(x) for x in d["connectedContact"]]

class terminal(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['termContacts'] = [ contact(x) for x in d["termContacts"]]

class PowerGrid(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['metals'] = [ Metal(x) for x in d["metals"]]
        self.__dict__['vias'] = [ Via(x) for x in d["vias"]]

class PowerNet(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['Pins'] = [ pin(x) for x in d["Pins"]]
        self.__dict__['connected'] = [ connectNode(x) for x in d["Pins"]]
        self.__dict__['dummy_connected'] = [ connectNode(x) for x in d["Pins"]]
        self.__dict__['path_metal'] = [ Metal(x) for x in d["path_metal"]]
        self.__dict__['path_via'] = [ Via(x) for x in d["path_via"]]

class pin(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['pinContacts'] = [ contact(x) for x in d["pinContacts"]]
        self.__dict__['pinVias'] = [ Via(x) for x in d["pinVias"]]

class contact(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['originBox'] = bbox(d["originBox"])
        self.__dict__['placedBox'] = bbox(d["placedBox"])
        self.__dict__['originCenter'] = point(d["originCenter"])
        self.__dict__['placedCenter'] = point(d["placedCenter"])

class globalContact(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['conTact'] = contact(d["conTact"])

class connectNode(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class layoutAS(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['Blocks'] = [ blockComplex(x) for x in d["Blocks"]]
        self.__dict__['Nets'] = [ net(x) for x in d["Nets"]]
        self.__dict__['Terminals'] = [ terminal(x) for x in d["Terminals"]]        

class SymmNet(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)
        self.__dict__['net1'] = net(d["net1"])
        self.__dict__['net2'] = net(d["net2"])

class SymmPairBlock(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class Preplace(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class Alignment(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class Abument(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class MatchBlock(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class PortPos(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class AlignBlock(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class CCCap(FallbackJSON):
    def __init__(self, d):    
        super().__init__(d)

class hierNode(FallbackJSON):
    def __init__(self, d):
        super().__init__(d)
        self.__dict__['Blocks'] = [ blockComplex(x) for x in d["Blocks"]]
        self.__dict__['Nets'] = [ net(x) for x in d["Nets"]]
        self.__dict__['Terminals'] = [ terminal(x) for x in d["Terminals"]]
        self.__dict__['Vdd'] = PowerGrid(d["Vdd"])
        self.__dict__['Gnd'] = PowerGrid(d["Gnd"])
        self.__dict__['PowerNets'] = [ PowerNet(x) for x in d["PowerNets"]]
        self.__dict__['blockPins'] = [ pin(x) for x in d["blockPins"]]
        self.__dict__['interMetals'] = [ contact(x) for x in d["interMetals"]]
        self.__dict__['interVias'] = [ Via(x) for x in d["interVias"]]
        self.__dict__['PnRAS'] = [ layoutAS(x) for x in d["PnRAS"]]

        self.__dict__['SNets'] = [ SymmNet(x) for x in d["SNets"]]
        self.__dict__['SPBlocks'] = [ SymmPairBlock(x) for x in d["SPBlocks"]]
        self.__dict__['Preplace_blocks'] = [ Preplace(x) for x in d["Preplace_blocks"]]
        self.__dict__['Alignment_blocks'] = [ Alignment(x) for x in d["Alignment_blocks"]]
        self.__dict__['Align_blocks'] = [ AlignBlock(x) for x in d["Align_blocks"]]
        self.__dict__['Abument_blocks'] = [ Abument(x) for x in d["Abument_blocks"]]
        self.__dict__['Match_blocks'] = [ MatchBlock(x) for x in d["Match_blocks"]]
        self.__dict__['CC_Caps'] = [ CCCap(x) for x in d["CC_Caps"]]
        self.__dict__['Port_Location'] = [ PortPos(x) for x in d["Port_Location"]]


def ff( x):
    def f(x):
        return None if x is None else globals()[x]
    if isinstance( x, tuple):
        assert x[0] is list
        return (list, f(x[1]))
    else:
        return f(x)

structs = [ (globals()[k], [(nm,ff(vv)) for (nm,vv) in v]) for (k,v) in abstract_structs]

class PnRDBEncoder(json.JSONEncoder):
    def default(self, obj):
        def f(x,v):
            assert v is None or isinstance( x, v)
            return x if v is None else self.default(x)

        for (klass,fields) in structs:
            if isinstance(obj, klass):
                return {k : ( [f(x,v[1]) for x in a] if isinstance( v, tuple) and v[0] is list else f(a,v)) for (k,v) in fields for a in (getattr(obj,k),)}

        return json.JSONEncoder.default(self, obj)
