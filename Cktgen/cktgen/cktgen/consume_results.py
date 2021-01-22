
import json
from .cktgen import parse_lgf, convert_align_to_adr
from .transformation import Rect, Transformation

def consume_results(args,tech):
    assert args.no_interface, "Removed support for 'interface'."

    with open( 'out/' + args.block_name + '.lgf', 'rt') as fp:  
      netl = parse_lgf( fp)

    placer_results = None  
    if args.placer_json != "":
      with open( args.placer_json, 'rt') as fp:  
        placer_results = json.load( fp)

        
    terminals = []
    if placer_results is not None:
      leaves_map = { leaf['template_name'] : leaf for leaf in placer_results['leaves']}

      for inst in placer_results['instances']:
        leaf = leaves_map[inst['template_name']]
        tr = inst['transformation']
        trans = Transformation( tr['oX'], tr['oY'], tr['sX'], tr['sY'])
        r = trans.hitRect( Rect( *leaf['bbox'])).canonical()

        nm = placer_results['nm'] + '/' + inst['instance_name'] + ':' + inst['template_name']
        terminals.append( { "netName" : nm, "layer" : "cellarea", "rect" : r.toList()})

        fa_map = inst['formal_actual_map']

        for term in leaf['terminals']:
            term = convert_align_to_adr(term)
            r = trans.hitRect( Rect( *term['rect'])).canonical()

            f = term['net_name']
            if f is not None:
                a = fa_map.get( f, inst['instance_name'] + "/" + f)
            else:
                a = None

            terminals.append( { "netName" : a,
                                "layer": term['layer'],
                                "rect": r.toList()})
      
    netl.write_input_file( netl.nm + "_xxx.txt")

    netl.dumpGR( tech, "INPUT/" + args.block_name + "_dr_globalrouting.json", cell_instances=terminals, no_grid=args.small)

