from . import lef_parser
import json

def lef_txt_to_layout_d( txt, nm=None):
    p = lef_parser.LEFParser()
    p.parse(txt)

    if nm is None:
        assert len(p.macros) == 1
        nm = p.macros[0].macroName

    tbl = {}
    for macro in p.macros:
        assert macro.macroName not in tbl
        tbl[macro.macroName] = macro

    macro = tbl[nm]

    bbox = macro.bbox
    terminals = []

    for pin in macro.pins:
        for (ly,tup) in pin.ports:
            r = list(tup)
            terminals.append( { 'netName': pin.nm, 'pin': pin.nm, 'layer': ly, 'rect': r})

    for (ly,tup) in macro.obs.ports:
        r = list(tup)
        terminals.append( { 'netName': None, 'layer': ly, 'rect': r})

    return {
        "bbox": bbox,
        "globalRoutes": [],
        "globalRouteGrid": [],
        "terminals": terminals
    }

def lef_to_json( fn, nm=None):
    with open( fn, "rt") as fp:
        txt = fp.read()

    with open( f"{nm}.json", "wt") as fp:
        json.dump( lef_txt_to_layout_d( txt, nm), fp=fp, indent=2)
    
