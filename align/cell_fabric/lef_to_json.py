from . import lef_parser
import json

def lef_to_json( fn, nm=None):
    with open( fn, "rt") as fp:
        txt = fp.read()
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
            terminals.append( { 'netName': pin.nm, 'layer': ly, 'rect': r})

    for (ly,tup) in macro.obs.ports:
        r = list(tup)
        terminals.append( { 'netName': None, 'layer': ly, 'rect': r})

    with open( f"{nm}.json", "wt") as fp:
        json.dump( { "bbox": bbox, "globalRoutes": [], "globalRouteGrid": [], "terminals": terminals}, fp=fp, indent=2)
