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


import copy

for (k,v) in abstract_structs:

    def capture_closure( k, v):
        def init_fn(self, d):
            for (nm,vv) in v:
                def f( x, vv):
                    if vv is None:
# might be faster if we don't do the copy
                        return copy.deepcopy( x)
                    else:
                        klass = globals()[vv]
                        return klass(x)

                if isinstance( vv, tuple):
                    assert vv[0] is list
                    setattr( self, nm, [ f(x,vv[1]) for x in d[nm]])
                else:
                    setattr( self, nm, f(d[nm],vv))
        return init_fn

    globals()[k] = type( k, (), { "__init__" : capture_closure( k, v)})

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
