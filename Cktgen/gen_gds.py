
import json
import pathlib
import re

from align.cell_fabric.gen_gds_json import translate_data
from align.cell_fabric import pdk

if __name__ == "__main__":
    with open("comparator.json", "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea"])

    layer_tbl = { "poly": "Poly",
                  "diffcon": "Diffcon",
                  "polycon": "Polycon",
                  "nwell": "Nwell",
                  "pdiff": "Pdiff",
                  "ndiff": "Ndiff",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2"}


    terminals = []
    for term in d['terminals']:
        ly = term['layer']
        if ly in skip_layers: continue
        term['layer'] = layer_tbl.get( ly, ly)
        terminals.append( term)
    d['terminals'] = terminals

    pdkfile = pathlib.Path('Intel/Intel_P1222p2_PDK/layers.json')
    p = pdk.Pdk().load(pdkfile)

    exclude_pattern = re.compile( r'^.*_gr$')

    dd = translate_data( "comparator", exclude_pattern, p.layerfile, 1, d, p.get_via_table()) 

    with open("comparator.gds.json", "wt") as fp:
        json.dump( dd, fp=fp, indent=2)
