import json
import logging

from . import lef_parser

logger = logging.getLogger(__name__)

def lef_txt_to_layout_d( txt, nm=None, *, scale_factor=10, m1pitch=None, m2pitch=None):
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

    # 1nm/scale_factor are the layout_json units
    # 1um/macro.scale_factor are the lef units
    # to convert nm to nm, mult by 1
    # to convert um to angstroms, mult by 10000
    # to convert nm to angstroms, mult by 10

    def ss( s):
        q = (1000*scale_factor*s)/macro.scale_factor
        qq = int(round(q,0))
        if abs(q-qq) > 0.001:
            logger.warning( f'Rounding removes precision {q} {qq}')
        return qq

    def sr( r):
        return [ss( s) for s in r]

    terminals = []

    for pin in macro.pins:
        for (ly,r) in pin.ports:
            scaled_r = sr(r)

            if m2pitch is not None and ly == 'M2':
                cy = (scaled_r[1] + scaled_r[3])//2
                if cy % m2pitch != 0:
                    logger.warning( f"M2 pin {pin.nm} not on grid {cy} {cy%m2pitch}")
            if m1pitch is not None and (ly == 'M1' or ly == 'M3'):
                cx = (scaled_r[0] + scaled_r[2])//2
                if cx % m1pitch != 0:
                    logger.warning( f"M1 pin {pin.nm} not on grid {cx} {cx%m1pitch}")

            terminals.append( { 'netName': pin.nm, 'pin': pin.nm, 'layer': ly, 'rect': scaled_r})

    if macro.obs is not None:
        for (ly,r) in macro.obs.ports:
            terminals.append( { 'netName': None, 'layer': ly, 'rect': sr(r)})

    scaled_bbox = sr(macro.bbox)
    if m2pitch is not None:
        h = scaled_bbox[3]
        if h % m2pitch != 0:
            logger.warning( f"bbox height not on grid {h} {h%m2pitch}")
    if m1pitch is not None:
        w = scaled_bbox[2]
        if w % m1pitch != 0:
            logger.warning( f"bbox width not on grid {w} {w%m1pitch}")

    return {
        "bbox": scaled_bbox,
        "globalRoutes": [],
        "globalRouteGrid": [],
        "terminals": terminals
    }

def lef_to_json( fn, nm=None, *, scale_factor=10, m1pitch=None, m2pitch=None):
    with open( fn, "rt") as fp:
        txt = fp.read()

    with open( f"{nm}.json", "wt") as fp:
        json.dump( lef_txt_to_layout_d( txt, nm, scale_factor=scale_factor, m1pitch=m1pitch, m2pitch=m2pitch), fp=fp, indent=2)
    
