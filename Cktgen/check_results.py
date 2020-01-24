
import json
import pathlib
import re
from pprint import pformat

from align.cell_fabric import transformation

from Intel.Intel_P1222p2_PDK.IntelP1222p2Canvas import IntelP1222p2Canvas

if __name__ == "__main__":
    with open("comparator.json", "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea", "ndiff", "pdiff", "nwell", "poly", "gcn"])

    layer_tbl = { "diffcon": "Diffcon",
                  "polycon": "Polycon",
                  "nwell": "Nwell",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2"}


    p = re.compile( "^(.*)_gr$")

    def s( r):
        assert all( v%10 == 0 for v in r)
        return [ v//10 for v in r]

    terminals = []
    for term in d['terminals']:
        ly = term['layer']
        if ly in skip_layers:
            continue
        nm = term['netName'] if 'netName' in term else term['net_name']
        if nm is not None and p.match(nm): continue
        term['layer'] = layer_tbl.get( ly, ly)
        term['rect'] = s(term['rect'])
        terminals.append( term)
    d['terminals'] = terminals

    pdkfile = pathlib.Path('Intel/Intel_P1222p2_PDK/layers.json')
    cnv = IntelP1222p2Canvas(pdkfile)

    cnv.bbox = transformation.Rect( *s(d['bbox']))
    cnv.terminals = d['terminals']

    cnv.gen_data(run_pex=False)
    
    if False:
        assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
        assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
        assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
        assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
