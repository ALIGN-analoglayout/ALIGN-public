
import json
import re
from ..cell_fabric.transformation import Rect, Transformation

from .base import Netlist

from .converters import convert_align_to_adr

def parse_lgf( fp):

  netl = None

  p_cell = re.compile( r'^Cell\s+(\S+)\s+bbox=(\S+):(\S+):(\S+):(\S+)\s*$')
  p_wire = re.compile( r'^Wire\s+net=(\S+)\s+(gid=(\S+)\s+|)layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)\s*$')

  p_wire2 = re.compile( r'^Wire\s+net=(\S+)\s+layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)(\s+gid=(\S+)|)\s*$')

  p_wire_in_obj = re.compile( r'^\s+Wire\s+net=(\S+)\s+layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)\s*$')

  p_obj = re.compile( r'^Obj\s+net=(\S+)\s+gen=(\S+)\s+x=(\S+)\s+y=(\S+)\s*$')

  p_obj_lbrace = re.compile( r'^Obj\s+net=(\S+)\s+gen=(\S+)\s+x=(\S+)\s+y=(\S+)\s*{\s*$')

  p_rbrace = re.compile( r'^\s*}\s*$')

  p_space = re.compile( r'^\s*$')

  if True:
    for line in fp:
      line = line.rstrip( '\n')
      
      m = p_cell.match( line)
      if m:
        cell = m.groups()[0]
        bbox = Rect( int(m.groups()[1]), int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]))

        netl = Netlist( cell, bbox)
        continue

      m = p_wire.match( line)
      if m:
        net = m.groups()[0]
        gid = m.groups()[2]
        if gid is not None: gid = int(gid)
        layer = m.groups()[3]
        rect = Rect( int(m.groups()[4]), int(m.groups()[5]), int(m.groups()[6]), int(m.groups()[7]))

        # hack to get rid of large global routing visualization grid
        if layer != "nwell":
          w = netl.newWire( net, rect, layer)
          w.gid = gid

        continue

      m = p_wire2.match( line)
      if m:
        net = m.groups()[0]
        layer = m.groups()[1]
        rect = Rect( int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]), int(m.groups()[5]))
        gid = m.groups()[7]
        if gid is not None: gid = int(gid)

        # hack to get rid of large global routing visualization grid
        if layer != "nwell":
          w = netl.newWire( net, rect, layer)
          w.gid = gid

        continue

      m = p_obj.match( line)
      if m:
        net = m.groups()[0]
        continue

      m = p_obj_lbrace.match( line)
      if m:
        net = m.groups()[0]
        continue

      m = p_wire_in_obj.match( line)
      if m:
        net = m.groups()[0]
        layer = m.groups()[1]
        rect = Rect( int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]), int(m.groups()[5]))

        if True or layer in ["via0","via1","via2","via3","via4"]:
          w = netl.newWire( net, rect, layer)
          w.gid = None

        continue

      m = p_rbrace.match( line)
      if m:

        continue

      m = p_space.match( line)
      if m: continue

      assert False, line

  return netl

def main(args,tech):
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

