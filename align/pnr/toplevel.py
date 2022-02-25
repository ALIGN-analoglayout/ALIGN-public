import logging
import re
import pathlib
import json
import copy
import collections
from collections import defaultdict
from itertools import chain

from .. import PnR
from .placer import hierarchical_place

from .render_placement import gen_placement_verilog, scale_placement_verilog, gen_boxes_and_hovertext, standalone_overlap_checker, scalar_rational_scaling, round_to_angstroms
from .build_pnr_model import PnRdatabase, NType, Omark
#from .checker import check_placement, check_place_on_grid
from ..gui.mockup import run_gui
from ..schema.hacks import List, FormalActualMap, VerilogJsonTop, VerilogJsonModule
from .hpwl import calculate_HPWL_from_placement_verilog_d, gen_netlist

from .grid_constraints import gen_constraints

import math

logger = logging.getLogger(__name__)

Omark = PnR.Omark
TransformType = PnR.TransformType

def write_verilog_json(verilog_d):
    return {"modules":[{"name":m.name,
                        "parameters": list(m.parameters),
                        "constraints": [mc.dict() for mc in m.constraints],
                        "instances": [mi.dict() for mi in m.instances],
                        } for m in verilog_d.modules],
        "global_signals":verilog_d.global_signals}

def route_single_variant( DB, drcInfo, current_node, lidx, opath, adr_mode, *, PDN_mode, return_name=None, noGDS=False, noExtra=False):
    DB.ExtractPinsToPowerPins(current_node)
    
    h_skip_factor = DB.getDrc_info().Design_info.h_skip_factor
    v_skip_factor = DB.getDrc_info().Design_info.v_skip_factor

    signal_routing_metal_l = DB.getDrc_info().Design_info.signal_routing_metal_l
    signal_routing_metal_u = DB.getDrc_info().Design_info.signal_routing_metal_u

    curr_route = PnR.Router()

    def RouteWork( mode, current_node, *, metal_l=signal_routing_metal_l, metal_u=signal_routing_metal_u, fn=''):
        curr_route.RouteWork( mode, current_node, drcInfo,
                              metal_l, metal_u,
                              h_skip_factor, v_skip_factor, fn)

    RouteWork( 6 if adr_mode else 4, current_node)

    if not noExtra:
        logger.debug( "Start WriteGcellGlobalRoute")
        if current_node.isTop:
            DB.WriteGcellGlobalRoute(current_node, f'{current_node.name}_GcellGlobalRoute_{lidx}.json', opath)
        else:
            current_node_copy = PnR.hierNode(current_node)
            DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
            DB.WriteGcellGlobalRoute(
                current_node_copy,
                f'{current_node_copy.name}_GcellGlobalRoute_{current_node_copy.n_copy}_{lidx}.json', opath)
        logger.debug("End WriteGcellGlobalRoute" )

    RouteWork( 5, current_node)

    if not noExtra:
        if current_node.isTop:
            DB.WriteJSON(current_node, True, True, False, False, f'{current_node.name}_DR_{lidx}', drcInfo, opath)
        else:
            current_node_copy = PnR.hierNode(current_node)
            DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
            DB.WriteJSON(current_node_copy, True, True, False, False,
                         f'{current_node_copy.name}_DR_{current_node_copy.n_copy}_{lidx}', drcInfo, opath)
            current_node.gdsFile = current_node_copy.gdsFile

    if current_node.isTop:
        power_grid_metal_l = DB.getDrc_info().Design_info.power_grid_metal_l
        power_grid_metal_u = DB.getDrc_info().Design_info.power_grid_metal_u

        power_routing_metal_l = DB.getDrc_info().Design_info.power_routing_metal_l
        power_routing_metal_u = DB.getDrc_info().Design_info.power_routing_metal_u

        # Power Grid Simulation
        if PDN_mode:
            current_node_copy = PnR.hierNode(current_node)

            current_file = "InputCurrent_initial.txt"
            power_mesh_conffile = "Power_Grid_Conf.txt"
            dataset_generation = True
            if dataset_generation:
                total_current = 0.036
                current_number = 20
                DB.Write_Current_Workload(current_node_copy, total_current, current_number, current_file)
                DB.Write_Power_Mesh_Conf(power_mesh_conffile)

            # Do we need to override these values?
            power_grid_metal_l = 4
            power_grid_metal_u = 5
            RouteWork(7, current_node_copy, metal_l=power_grid_metal_l, metal_u=power_grid_metal_u, fn=power_mesh_conffile)

            logger.info("Start MNA ")
            output_file_IR = "IR_drop.txt"
            output_file_EM = "EM.txt"
            Test_MNA = PnR.MNASimulationIfc(current_node_copy, drcInfo, current_file, output_file_IR, output_file_EM)
            worst = Test_MNA.Return_Worst_Voltage()
            logger.info(f"worst voltage is {worst}")
            Test_MNA.Clear_Power_Grid(current_node_copy.Vdd)
            Test_MNA.Clear_Power_Grid(current_node_copy.Gnd)
            logger.info("End MNA")
            #return

        
        RouteWork(2, current_node, metal_l=power_grid_metal_l, metal_u=power_grid_metal_u)

        if not noExtra:
            DB.WriteJSON(current_node, True, True, False, True, f'{current_node.name}_PG_{lidx}', drcInfo, opath)

        logger.debug("Checkpoint : Starting Power Routing");
        
        RouteWork(3, current_node, metal_l=power_routing_metal_l, metal_u=power_routing_metal_u)

        if not noExtra:
            DB.WriteJSON(current_node, True, False, True, True, f'{current_node.name}_PR_{lidx}', drcInfo, opath)
            DB.Write_Router_Report(current_node, opath)

    # transform current_node into current_node coordinate
    if not noGDS:
        if current_node.isTop:
            return_name = f'{current_node.name}_{lidx}' if return_name is None else return_name
            DB.WriteJSON(current_node, True, True, True, True, return_name, drcInfo, opath)
            DB.WriteLef(current_node, f'{return_name}.lef', opath)
            # DB.PrintHierNode(current_node)
        else:
            current_node_copy = PnR.hierNode(current_node)
            DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
            return_name = f'{current_node_copy.name}_{current_node_copy.n_copy}_{lidx}' if return_name is None else return_name
            DB.WriteJSON(current_node_copy, True, True, True, True, return_name, drcInfo, opath)
            current_node.gdsFile = current_node_copy.gdsFile
            DB.WriteLef(current_node_copy, f'{return_name}.lef', opath)
            # DB.PrintHierNode(current_node_copy)
    else:
        if current_node.isTop:
            return_name = f'{current_node.name}_{lidx}' if return_name is None else return_name
        else:
            return_name = f'{current_node.name}_{current_node.n_copy}_{lidx}' if return_name is None else return_name
            current_node.gdsFile = f'{opath}{return_name}.gds'

    return return_name

def route_bottom_up( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS, placements_to_run, nroutings):

    if placements_to_run is None:
        placements_to_run = list(range(min(nroutings, DB.hierTree[idx].numPlacement)))

    # Compute all the needed subblocks
    subblocks_d = defaultdict(set)

    def aux(idx, sel):
        subblocks_d[idx].add(sel)
        current_node = DB.CheckoutHierNode(idx, sel) # Make a copy
        for blk in current_node.Blocks:
            child_idx = blk.child
            if child_idx >= 0:
                aux(child_idx, blk.selectedInstance)

    for lidx in placements_to_run:
        aux(idx, lidx)

    results_name_map = {}

    TraverseOrder = DB.TraverseHierTree()

    assert idx == TraverseOrder[-1]

    new_currentnode_idx_d = {}

    for i in TraverseOrder:
        new_currentnode_idx_d[i] = {}
        for j in subblocks_d[i]:
            current_node = DB.CheckoutHierNode(i, j)  # Make a copy
            DB.hierTree[i].n_copy += 1

            logger.info( f'bottom up routing for {current_node.name} ({i}) placement version {j}')

            logger.debug( f'Existing parents: {current_node.parent}')
            # SMB: I think we should clear this and build up parents of the routing hN
            current_node.parent = []

            assert current_node.LL.x == 0
            assert current_node.LL.y == 0
            current_node.UR.x = current_node.width
            current_node.UR.y = current_node.height
            assert current_node.abs_orient == Omark.N

            # Remap using new bottom up hNs
            for bit,blk in enumerate(current_node.Blocks):
                child_idx = blk.child
                inst_idx = blk.selectedInstance
                if child_idx >= 0:
                    assert child_idx in new_currentnode_idx_d, f"Toporder incorrect {child_idx} {i} {TraverseOrder}"
                    assert inst_idx in new_currentnode_idx_d[child_idx], f"subblocks_d incorrect {child_idx} {inst_idx} {subblocks_d[child_idx]}"
                    
                    DB.CheckinChildnodetoBlock(current_node, bit, DB.hierTree[new_currentnode_idx_d[child_idx][inst_idx]], blk.instance[inst_idx].orient)
                    blk.child = new_currentnode_idx_d[child_idx][inst_idx]

            return_name = f'{current_node.name}_{j}'
            result_name = route_single_variant( DB, DB.getDrc_info(), current_node, j, opath, adr_mode, PDN_mode=PDN_mode, return_name=return_name, noGDS=skipGDS, noExtra=skipGDS)

            DB.AppendToHierTree(current_node)

            new_currentnode_idx_d[i][j] = len(DB.hierTree) - 1

            results_name_map[result_name] = ((f'{current_node.name}:placement_{j}',), new_currentnode_idx_d[i][j], DB)

            for blk in current_node.Blocks:
                if blk.child >= 0:
                    # Potential slug bug; uniqifying the vector each time
                    DB.hierTree[blk.child].parent = list(set(DB.hierTree[blk.child].parent + [ new_currentnode_idx_d[i][j] ]))
                    logger.debug( f'Set parent of {blk.child} to {DB.hierTree[blk.child].parent}')

    return results_name_map

def route_no_op( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS, placements_to_run, nroutings):
    results_name_map = {}
    return results_name_map

def route_top_down_aux( DB, drcInfo,
                        bounding_box,
                        current_node_ort, idx, lidx, sel,
                        opath, adr_mode, *, PDN_mode, results_name_map, hierarchical_path, skipGDS):

    current_node = DB.CheckoutHierNode(idx, sel) # Make a copy
    i_copy = DB.hierTree[idx].n_copy

    logger.debug( f'Start of route_top_down; placement idx {idx} lidx {lidx} nm {current_node.name} i_copy {i_copy}')

    DB.hierTree[idx].n_copy += 1

    current_node.LL = bounding_box.LL
    current_node.UR = bounding_box.UR
    current_node.abs_orient = current_node_ort
    DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, TransformType.Forward)

    for bit, blk in enumerate(current_node.Blocks):
        child_idx = blk.child
        if child_idx == -1: continue
        inst = blk.instance[blk.selectedInstance]
        childnode_orient = DB.RelOrt2AbsOrt( current_node_ort, inst.orient)
        child_node_name = DB.hierTree[child_idx].name
        childnode_bbox = PnR.bbox( inst.placedBox.LL, inst.placedBox.UR)
        new_childnode_idx = route_top_down_aux(DB, drcInfo, childnode_bbox, childnode_orient, child_idx, lidx, blk.selectedInstance, opath, adr_mode, PDN_mode=PDN_mode, results_name_map=results_name_map, hierarchical_path=hierarchical_path + (inst.name,), skipGDS=skipGDS)
        DB.CheckinChildnodetoBlock(current_node, bit, DB.hierTree[new_childnode_idx], DB.hierTree[new_childnode_idx].abs_orient)
        blk.child = new_childnode_idx

    result_name = route_single_variant( DB, drcInfo, current_node, lidx, opath, adr_mode, PDN_mode=PDN_mode, noGDS=skipGDS, noExtra=skipGDS)

    #results_name_map[result_name] = hierarchical_path

    if not current_node.isTop:
        DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, TransformType.Backward)

    hierTree_len = len(DB.hierTree)
    # Make sure the length of hierTree increased by one; this won't happend if you did the commented out line below
    #DB.hierTree.append( current_node)
    # It would if you did commented out line below but this requires a bunch of copying
    #DB.hierTree = DB.hierTree + [current_node]
    # Instead we added a custom method to do this
    DB.AppendToHierTree(current_node)
    assert len(DB.hierTree) == 1+hierTree_len
    new_currentnode_idx = len(DB.hierTree) - 1

    results_name_map[result_name] = (hierarchical_path, new_currentnode_idx, DB)


    for blk in current_node.Blocks:
        if blk.child == -1: continue
        # Set the whole array, not parent[0]; otherwise the python temporary is updated
        DB.hierTree[blk.child].parent = [ new_currentnode_idx ]
        logger.debug( f'Set parent of {blk.child} to {new_currentnode_idx} => DB.hierTree[blk.child].parent[0]={DB.hierTree[blk.child].parent[0]}')

    logger.debug( f'End of route_top_down; placement idx {idx} lidx {lidx} nm {current_node.name} i_copy {i_copy} new_currentnode_idx {new_currentnode_idx}')

    return new_currentnode_idx

def route_top_down( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS, placements_to_run, nroutings):
    assert len(DB.hierTree[idx].PnRAS) == DB.hierTree[idx].numPlacement

    if placements_to_run is None:
        placements_to_run = list(range(min(nroutings,DB.hierTree[idx].numPlacement)))

    results_name_map = {}
    new_topnode_indices = []
    for lidx in placements_to_run:
        sel = lidx
        new_topnode_idx = route_top_down_aux( DB, DB.getDrc_info(),
                                              PnR.bbox( PnR.point(0,0),
                                                        PnR.point(DB.hierTree[idx].PnRAS[lidx].width,
                                                                  DB.hierTree[idx].PnRAS[lidx].height)),
                                              Omark.N, idx, lidx, sel,
                                              opath, adr_mode, PDN_mode=PDN_mode, results_name_map=results_name_map,
                                              hierarchical_path=(f'{DB.hierTree[idx].name}:placement_{lidx}',),
                                              skipGDS=skipGDS
        )
        new_topnode_indices.append(new_topnode_idx)
    return results_name_map

def route( *, DB, idx, opath, adr_mode, PDN_mode, router_mode, skipGDS, placements_to_run, nroutings):
    logger.info(f'Starting {router_mode} routing on {DB.hierTree[idx].name} {idx} restricted to {placements_to_run}')

    router_engines = { 'top_down': route_top_down,
                       'bottom_up': route_bottom_up,
                       'no_op': route_no_op
                       }

    return router_engines[router_mode]( DB=DB, idx=idx, opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode, skipGDS=skipGDS, placements_to_run=placements_to_run, nroutings=nroutings)

def change_concrete_names_for_routing(scaled_placement_verilog_d):
    leaf_ctns = [leaf['concrete_name'] for leaf in scaled_placement_verilog_d['leaves']]

    p = re.compile(r'^(.+)_(\d+)$')
    cn_tbl = defaultdict(list)
    for module in scaled_placement_verilog_d['modules']:
        an = module['abstract_name']
        cn = module['concrete_name']
        m = p.match(cn)
        assert m
        stem, suffix = m.groups()
        assert stem == an
        cn_tbl[an].append(int(suffix))

    tr_tbl = {}
    for an, cn_indices in cn_tbl.items():
        for new_idx, old_idx in enumerate(sorted(cn_indices)):
            tr_tbl[f'{an}_{old_idx}'] = f'{an}_{new_idx}'

    logger.info(f'change_concrete_names_for_routing: {tr_tbl}')

    for module in scaled_placement_verilog_d['modules']:
        module['concrete_name'] = tr_tbl[module['concrete_name']]
        for instance in module['instances']:
            ctn = instance['concrete_template_name']
            if ctn in leaf_ctns:
                assert ctn not in tr_tbl
                instance['abstract_template_name'] = ctn
            else:
                assert ctn in tr_tbl
                instance['concrete_template_name'] = tr_tbl[ctn]                   

    for leaf in scaled_placement_verilog_d['leaves']:
        leaf['abstract_name'] =leaf['concrete_name']

    return tr_tbl

def gen_abstract_verilog_d( verilog_d):
    new_verilog_d = copy.deepcopy(verilog_d)

    if 'leaves' in new_verilog_d:
        new_verilog_d['leaves'] = None

    for module in new_verilog_d['modules']:
        assert 'concrete_name' in module
        assert 'abstract_name' in module
        assert 'name' not in module
        module['name'] = module['abstract_name']
        del module['abstract_name']        
        del module['concrete_name']        

        assert 'bbox' in module
        del module['bbox']

        for instance in module['instances']:
            assert 'concrete_template_name' in instance
            del instance['concrete_template_name']
            assert 'transformation' in instance
            del instance['transformation']

    return new_verilog_d


def place_and_route(*, DB, opath, fpath, numLayout, effort, adr_mode, PDN_mode, verilog_d,
                    router_mode, gui, skipGDS, lambda_coeff, scale_factor,
                    reference_placement_verilog_json, concrete_top_name, nroutings, select_in_ILP, seed,
                    use_analytical_placer, ilp_solver, primitives, toplevel_args, results_dir):

    reference_placement_verilog_d = None
    if reference_placement_verilog_json is not None:
        with open(reference_placement_verilog_json, "rt") as fp:
            reference_placement_verilog_d = json.load(fp)

    placements_to_run, placement_verilog_alternatives = hierarchical_place(DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort,
                                                                           verilog_d=verilog_d, gui=gui, lambda_coeff=lambda_coeff,
                                                                           scale_factor=scale_factor,
                                                                           reference_placement_verilog_d=reference_placement_verilog_d,
                                                                           concrete_top_name=concrete_top_name,
                                                                           select_in_ILP=select_in_ILP, seed=seed,
                                                                           use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver,
                                                                           primitives=primitives, run_cap_placer=True)

    pattern = re.compile(r'^(\S+)_(\d+)$')
    last_key = list(placement_verilog_alternatives.keys())[-1]
    m = pattern.match(last_key)
    assert m
    topname = m.groups()[0]

    assert nroutings == 1, f"nroutings other than 1 is currently not working"


    if placements_to_run is None:
        verilog_ds_to_run = [(f'{topname}_{i}', placement_verilog_alternatives[f'{topname}_{i}']) for i in range(min(nroutings, len(placement_verilog_alternatives)))]
    else:
        verilog_ds_to_run = [(f'{topname}_{i}', placement_verilog_alternatives[f'{topname}_{i}']) for i in placements_to_run]


    #
    # Hacks for partial routing
    #
    if primitives is not None:
        # Hack verilog_ds in place
        for concrete_top_name, verilog_d in verilog_ds_to_run:
            # Update connectivity for partially routed primitives
            for module in verilog_d['modules']:
                for instance in module['instances']:
                    ctn = instance['concrete_template_name']
                    if ctn in primitives:
                        primitive = primitives[ctn]
                        if 'metadata' in primitive and 'partially_routed_pins' in primitive['metadata']:
                            prp = primitive['metadata']['partially_routed_pins']
                            by_net = defaultdict(list)
                            for enity_name, net_name in prp.items():
                                by_net[net_name].append(enity_name)

                            new_fa_map = List[FormalActualMap]()
                            for fa in instance['fa_map']:
                                f, a = fa['formal'], fa['actual'] 
                                for enity_name in by_net.get(f, [f]):
                                    new_fa_map.append(FormalActualMap(formal=enity_name, actual=a))

                            instance['fa_map'] = new_fa_map

        
    res_dict = {}
    for concrete_top_name, scaled_placement_verilog_d in verilog_ds_to_run:

        tr_tbl = change_concrete_names_for_routing(scaled_placement_verilog_d)
        abstract_verilog_d = gen_abstract_verilog_d(scaled_placement_verilog_d)
        concrete_top_name0 = tr_tbl[concrete_top_name]

        # don't need to send this to disk; for debug only
        if True:
            logger.debug(f"updated verilog: {abstract_verilog_d}")
            verilog_file = toplevel_args[3]

            abstract_verilog_file = verilog_file.replace(".verilog.json", ".abstract_verilog.json")

            with (pathlib.Path(fpath)/abstract_verilog_file).open("wt") as fp:
                json.dump(abstract_verilog_d.dict(), fp=fp, indent=2, default=str)
                
            scaled_placement_verilog_file = verilog_file.replace(".verilog.json", ".scaled_placement_verilog.json")

            with (pathlib.Path(fpath)/scaled_placement_verilog_file).open("wt") as fp:
                json.dump(scaled_placement_verilog_d.dict(), fp=fp, indent=2, default=str)

        # create a fresh DB and populate it with a placement verilog d    

        lef_file = toplevel_args[2]
        new_lef_file = lef_file.replace(".placement_lef", ".lef")
        toplevel_args[2] = new_lef_file

        # Build up a new map file
        map_d_in = []
        idir = pathlib.Path(fpath)
        odir = pathlib.Path(opath)
        
        cc_caps = []

        for leaf in scaled_placement_verilog_d['leaves']:
            ctn = leaf['concrete_name']
            if   (idir/f'{ctn}.json').exists():
                map_d_in.append((ctn,str(idir/f'{ctn}.gds')))
            elif (odir/f'{ctn}.json').exists():
                map_d_in.append((ctn,str(odir/f'{ctn}.gds')))
                cc_caps.append(ctn)
            else:
                logger.error(f'Missing .lef file for {ctn}')

        lef_s_in = None
        if cc_caps:
            with (idir/new_lef_file).open("rt") as fp:
                lef_s_in = fp.read()
                
            for cc_cap in cc_caps:
                with (odir/f'{cc_cap}.lef').open("rt") as fp:
                    s = fp.read()
                    lef_s_in += s

        DB, new_verilog_d, new_fpath, new_opath, _, _ = gen_DB_verilog_d(toplevel_args, results_dir, verilog_d_in=abstract_verilog_d, map_d_in=map_d_in, lef_s_in=lef_s_in)
        
        assert new_verilog_d == abstract_verilog_d

        assert new_fpath == fpath
        assert new_opath == opath

        # need to populate the placement data

        placements_to_run, _ = hierarchical_place(DB=DB, opath=opath, fpath=fpath, numLayout=1, effort=effort,
                                                  verilog_d=abstract_verilog_d, gui=False, lambda_coeff=lambda_coeff,
                                                  scale_factor=scale_factor,
                                                  reference_placement_verilog_d=scaled_placement_verilog_d.dict(),
                                                  concrete_top_name=concrete_top_name0,
                                                  select_in_ILP=select_in_ILP, seed=seed,
                                                  use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver,
                                                  primitives=primitives, run_cap_placer=False)

        # populate new DB with placements to run

        res = route( DB=DB, idx=DB.TraverseHierTree()[-1], opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode,
                     router_mode=router_mode, skipGDS=skipGDS, placements_to_run=placements_to_run, nroutings=nroutings)

        res_dict.update(res)
    
    return res_dict


def gen_DB_verilog_d(args, results_dir, *, verilog_d_in=None, map_d_in=None, lef_s_in=None):
    assert len(args) == 9

    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]

    DB, verilog_d = PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile, verilog_d_in=verilog_d_in, map_d_in=map_d_in, lef_s_in=lef_s_in)

    assert verilog_d is not None

    if results_dir is None:
        opath = './Results/'
    else:
        opath = str(pathlib.Path(results_dir))
        if opath[-1] != '/':
            opath = opath + '/'

    pathlib.Path(opath).mkdir(parents=True,exist_ok=True)

    return DB, verilog_d, fpath, opath, numLayout, effort
    

def toplevel(args, *, PDN_mode=False, adr_mode=False, results_dir=None, router_mode='top_down',
             gui=False, skipGDS=False,
             lambda_coeff=1.0, scale_factor=2,
             reference_placement_verilog_json=None,
             concrete_top_name=None,
             nroutings=1, select_in_ILP=False,
             seed=0, use_analytical_placer=False, ilp_solver='symphony', primitives=None):

    DB, verilog_d, fpath, opath, numLayout, effort = gen_DB_verilog_d(args, results_dir)

    logger.debug(f'Using {ilp_solver} to solve ILP in placer')
    results_name_map = place_and_route(DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort,
                                       adr_mode=adr_mode, PDN_mode=PDN_mode,
                                       verilog_d=verilog_d, router_mode=router_mode, gui=gui, skipGDS=skipGDS,
                                       lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                       reference_placement_verilog_json=reference_placement_verilog_json,
                                       concrete_top_name=concrete_top_name,
                                       nroutings=nroutings, select_in_ILP=select_in_ILP,
                                       seed=seed, use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver,
                                       primitives=primitives, toplevel_args=args, results_dir=results_dir)

    return results_name_map

def toplevel_route_only(args, *, PDN_mode=False, adr_mode=False, results_dir=None, router_mode='top_down',
                        gui=False, skipGDS=False,
                        nroutings=1, select_in_ILP=False,
                        seed=0, use_analytical_placer=False):

    DB, verilog_d, fpath, opath, numLayout, effort = gen_DB_verilog_d(args)

    idx = 0
    results_name_map = route( DB=DB, idx=idx, opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode,
                              router_mode=router_mode, skipGDS=skipGDS, placements_to_run=None, nroutings=nroutings)

    return results_name_map
