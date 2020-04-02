
import json
import pathlib
import re
import argparse
from pprint import pformat

from align.cell_fabric import transformation

from intel_p1222p2.IntelP1222p2Canvas import IntelP1222p2Canvas

def check_results(ckt_name):

    if not ckt_name.endswith('.json'):
        ckt_name += '.json'

    with open( ckt_name, "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea", "ndiff", "pdiff", "nwell", "poly", "gcn", "polycon", "diffcon"])

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
        if str(ly).lower() in skip_layers:
            continue
        nm = term['netName'] if 'netName' in term else term['net_name']
        #
        # !kor and !float signals might be need. Right now, just excluding them.
        #
        if nm in ['!kor', '!float']: continue
        if nm is not None and p.match(nm): continue
        term['layer'] = layer_tbl.get( ly, ly)
        term['rect'] = s(term['rect'])
        terminals.append( term)
    d['terminals'] = terminals

    cnv = IntelP1222p2Canvas()

    cnv.bbox = transformation.Rect( *s(d['bbox']))
    cnv.terminals = d['terminals']

    data = cnv.gen_data(run_pex=True, run_drc=True)

    with open( ckt_name + "_prim.json", "w") as fp:
        cnv.writeJSON(fp)

    tbl = cnv.pex.getSummaryCaps()
    def diffs( n0, n1):
        a, b = tbl[n0], tbl[n1]
        s = (a+b)/2
        return f"{n0},{n1}: {a:.2f}f, {b:.2f}f, {100*(a/s-1):.1f}%, {100*(b/s-1):.1f}%"

    if ckt_name in ["comparator","comparator_kbc"]:
        print( diffs( 'vin', 'vip'))
        print( diffs( 'vin_d', 'vip_d'))
        print( diffs( 'vin_o', 'vip_o'))
        print( diffs( 'von', 'vop'))

    if True:
        assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
        assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
        assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
        assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)

    return(data)

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check <circuit>.JSON against design rules")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")

    args = parser.parse_args()

    check_results(args.circuit)
