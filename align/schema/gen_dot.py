from .parser import SpiceParser
from .types import set_context

def gen_dot_file(nm, ifn, ofn):

    parser = SpiceParser()
    # Patch library to use different model name
    parser.library.append(parser.library.find('PMOS').copy(update={'name': 'P'}))
    parser.library.append(parser.library.find('NMOS').copy(update={'name': 'N'}))
    parser.library.append(parser.library.find('PMOS').copy(update={'name': 'PFET'}))
    parser.library.append(parser.library.find('NMOS').copy(update={'name': 'NFET'}))

    with open( ifn, "rt") as fp:
        txt = fp.read()
        parser.parse(txt)

    q = parser.library.find(nm.upper())

    tbl = { "GND": {}, "VSS": {}, "VDD": {}, "CLK": {}}

    elements_no_dummys = []
    for e in q.elements:
        q = set(v for k,v in e.pins.items() if k != "B")
        if len(q) == 1: continue

        if 'D' in e.pins and 'S' in e.pins and e.pins['D'] == e.pins['S']:
            continue

        for k in tbl.keys():
            if k in q:
                tbl[k][e.name] = len(tbl[k])

        elements_no_dummys.append(e)


    with open( ofn, "wt") as fp:
        print( "graph G {", file=fp)
        print( "\tnode[shape=record]", file=fp)

        for e in elements_no_dummys:
            if   e.model in ("NMOS", "N", "NFET"):
                print( f"\t{e.name} [label=\"{{ {e.name}|<f0>d|<f1>g|<f2>s}}\"]", file=fp)
            elif e.model in ("PMOS", "P", "PFET"):
                print( f"\t{e.name} [label=\"{{<f2>s|<f1>g|<f0>d|{e.name} }}\"]", file=fp)
            elif e.model == "CAP":
                print( f"\t{e.name} [label=\"{{ {e.name}|<f1>+|<f0>- }}\"]", file=fp)
            else:
                assert False, e.model

        # lst = []
        # for e in elements_no_dummys:
        #     if e.model == "NMOS":
        #         lst.append( e.name)

        # if lst:
        #     s = ','.join(lst)
        #     print( f"\t{{ rank=same; {s} }}", file=fp)

        # lst = []
        # for e in elements_no_dummys:
        #     if e.model == "PMOS":
        #         lst.append( e.name)

        # if lst:
        #     s = ','.join(lst)
        #     print( f"\t{{ rank=same; {s} }}", file=fp)

        nets = { v for e in elements_no_dummys for v in e.pins.values() }

        print( "\tnode[shape=circle]", file=fp)
        for n in nets:
            if n not in tbl:
                print( f"\t{n} [label=\"{n}\"]", file=fp)

        for n,vv in tbl.items():
            for _,idx in vv.items():
                print( f"\t{n}{idx} [label=\"{n}\"]", file=fp)

        m = { "S": "f2", "G": "f1", "D": "f0"}
        m_cap = { "+": "f1", "-": "f0"}

        for e in elements_no_dummys:
            for k,v in e.pins.items():
                if k in m:
                    vv = f"{v}{tbl[v][e.name]}" if v in tbl and e.name in tbl[v] else v
                    if k in ["S"]     and e.model == "PMOS" or \
                       k in ["D","G"] and e.model == "NMOS":
                        print( f"\t{vv} -- {e.name}:{m[k]}", file=fp)
                    else:
                        print( f"\t{e.name}:{m[k]} -- {vv}", file=fp)
                if k in m_cap:
                    vv = f"{v}{tbl[v][e.name]}" if v in tbl and e.name in tbl[v] else v
                    print( f"\t{e.name}:{m_cap[k]} -- {vv}", file=fp)

        print( "}", file=fp)
