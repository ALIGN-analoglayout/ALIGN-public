
import json
import pathlib
import re
import argparse
from pprint import pformat

from align.cell_fabric import transformation

from intel_p1222p2.IntelP1222p2Canvas import IntelP1222p2Canvas

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check <circuit>.JSON against design rules")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")

    args = parser.parse_args()

    ckt_name = args.circuit

    with open( ckt_name + ".json", "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea", "ndiff", "pdiff", "nwell", "poly", "gcn"])

    layer_tbl = { "diffcon": "Diffcon",
                  "polycon": "Polycon",
                  "nwell": "Nwell",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "metal4": "M4",
                  "metal5": "M5",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2",
                  "via3": "V3",
                  "via4": "V4"}

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

    pdkfile = pathlib.Path('Intel/intel_p1222p2/layers.json')
    cnv = IntelP1222p2Canvas(pdkfile)

    cnv.bbox = transformation.Rect( *s(d['bbox']))
    cnv.terminals = d['terminals']

    cnv.gen_data(run_pex=True)

    tbl = cnv.pex.getSummaryCaps()
    def diffs( n0, n1):
        a, b = tbl[n0], tbl[n1]
        s = (a+b)/2
        return f"{n0},{n1}: {a:.2f}f, {b:.2f}f, {100*(a/s-1):.1f}%, {100*(b/s-1):.1f}%"

    if ckt_name == "comparator":
        print( diffs( 'vin', 'vip'))
        print( diffs( 'vin_d', 'vip_d'))
        print( diffs( 'vin_o', 'vip_o'))
        print( diffs( 'von', 'vop'))

    if False:
        assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
        assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
        assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
        assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
