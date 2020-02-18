
import json
import pathlib
import re
import argparse
from pprint import pformat
from itertools import cycle
from align.cell_fabric import transformation

from intel_p1222p2.IntelP1222p2Canvas import IntelP1222p2Canvas

def route_power(cnv, metal, power='vcc_0p9', ground='vssx'):

    assert metal.startswith('M')
    assert int(metal[1:]) > 2

    prev_metal = 'M' + str(int(metal[1:])-1)
    prev_via   = 'V' + str(int(metal[1:])-1)

    via_half_width_x = cnv.pdk[prev_via]['WidthX']//2
    via_half_width_y = cnv.pdk[prev_via]['WidthY']//2

    metal_dir = cnv.pdk[metal]['Direction'].upper()

    bbox = cnv.bbox.toList()
    cl_min,cl_max = (bbox[1],bbox[3]) if metal_dir == 'H' else (bbox[0],bbox[2])
    sp_min,sp_max = (bbox[0],bbox[2]) if metal_dir == 'H' else (bbox[1],bbox[3])

    sp_min = sp_min - cnv.pdk[prev_metal]['Pitch']//2
    sp_max = sp_max + cnv.pdk[prev_metal]['Pitch']//2

    tcl_min = 2*(cnv.pdk[metal]['Offset'] + cnv.pdk[metal]['Pitch']*(cl_min//cnv.pdk[metal]['Pitch'] + 1))
    tcl_max = 2*(cnv.pdk[metal]['Offset'] + cnv.pdk[metal]['Pitch']*(cl_max//cnv.pdk[metal]['Pitch']))

    pattern = ['!kor',power,'!kor',ground,'!kor']
    generate_net = cycle(pattern)

    def check_via_enclosure(prev_via, via_r, prev_metal, prev_metal_r, metal, metal_r):

        def check_single_metal( via_r, metal, metal_r, enclosure_value):
            o = 0 if cnv.pdk[metal]['Direction'].upper() == 'H' else 1
            if (metal_r[o+0] > via_r[o+0] - enclosure_value) or (metal_r[o+2] < via_r[o+2] + enclosure_value):
                return(False)
            else:
                return(True)

        r1 = check_single_metal( via_r, prev_metal, prev_metal_r, cnv.pdk[prev_via]['VencA_L'])
        r2 = check_single_metal( via_r, metal,      metal_r,      cnv.pdk[prev_via]['VencA_H'])
        if r1 and r2:
            return(True)
        else:
            return(False)

    for tcl in range(tcl_min, tcl_max, 2*cnv.pdk[metal]['Pitch']):
        net = next(generate_net)
        # Add a track if there is no obstruction
        if tcl not in cnv.rd.store_scan_lines[metal]:
            c0 = tcl//2 - cnv.pdk[metal]['Width']//2
            c1 = tcl//2 + cnv.pdk[metal]['Width']//2
            metal_r = [sp_min, c0, sp_max, c1] if metal_dir == 'H' else [c0, sp_min, c1, sp_max]
            term = {'layer': metal, 'netName': net, 'rect': metal_r}
            cnv.terminals.append(term)

            if (net == '!kor'): continue
            # TODO: Ignore DRC errors on !kor or signals mathing a pattern.. silence opens reported by removeduplicate

            tcl_prev_prev = None
            # Add via if overlapping with previous layer
            for tcl_prev in cnv.rd.store_scan_lines[prev_metal]:
                if tcl_prev_prev is not None:
                    if ( tcl_prev - tcl_prev_prev == cnv.pdk[prev_metal]['Pitch']):
                        continue
                for term in cnv.rd.store_scan_lines[prev_metal][tcl_prev].rects:
                    if term.netName == net:
                        prev_metal_r = term.rect
                        o = 1 if metal_dir == 'H' else 0
                        sp0, sp1 = (prev_metal_r[o+0],prev_metal_r[o+2])
                        xc,yc = [tcl//2, tcl_prev//2] if metal_dir == 'V' else [tcl_prev//2, tcl//2]
                        r = [xc-via_half_width_x, yc-via_half_width_y, xc+via_half_width_x, yc+via_half_width_y]

                        if( check_via_enclosure(prev_via, r, prev_metal, prev_metal_r, metal, metal_r) ):
                            term = {'layer': prev_via, 'netName': net, 'rect': r}
                            cnv.terminals.append(term)
                            tcl_prev_prev = tcl_prev
    pass

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check <circuit>.JSON against design rules")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")
    parser.add_argument("--power",   required=True, type=str, help="Power net name")
    parser.add_argument("--ground",  required=True, type=str, help="Ground net name")

    args = parser.parse_args()

    ckt_name = args.circuit

    with open( ckt_name + ".json", "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea", "ndiff", "pdiff", "nwell", "poly", "gcn"])
    skip_layers = set( ["boundary", "diearea", "cellarea"])

    layer_tbl = { "metal1": "M1",
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
        #
        # !kor and !float signals might be need. Right now, just excluding them.
        #
        # if nm in ['!kor', '!float']: continue
        if nm is not None and p.match(nm): continue
        term['layer'] = layer_tbl.get( ly, ly)
        term['rect'] = s(term['rect'])
        terminals.append( term)
    d['terminals'] = terminals

    pdkfile = pathlib.Path('Intel/intel_p1222p2/layers.json')
    cnv = IntelP1222p2Canvas(pdkfile)

    cnv.bbox = transformation.Rect( *s(d['bbox']))
    cnv.terminals = d['terminals']

    for m in ['M3','M4','M5']:
        cnv.gen_data(run_pex=False, run_drc=False)
        route_power(cnv, m, power=args.power, ground=args.ground)

    print('========= IGNORE ERRORS ABOVE THIS LINE =========')

    cnv.gen_data(run_pex=True, run_drc=True)

    with open( ckt_name + "_drc.json", "w") as fp:
        cnv.writeJSON(fp)

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
