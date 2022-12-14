import plotly.graph_objects as go
import plotly.express as px

import logging
import pathlib
import json
import re
from ..cell_fabric import transformation

from collections import defaultdict

from .. import PnR
from .manipulate_hierarchy import change_concrete_names_for_routing, gen_abstract_verilog_d, connectivity_change_for_partial_routing

from .build_pnr_model import gen_DB_verilog_d
from .placer import hierarchical_place

from .pythonic_router import collect_pins


logger = logging.getLogger(__name__)

Omark, NType = PnR.Omark, PnR.NType
TransformType = PnR.TransformType

def route_single_variant( DB, drcInfo, current_node, lidx, opath, adr_mode, *, PDN_mode, return_name=None, noGDS=False, noExtra=False):

    # Hack to read in default layers
    # This can be removed once default and per net layer restrictions are handled in the router

    ipath = pathlib.Path("./inputs")
    pnr_constraint_fn = ipath / f'{current_node.name}.pnr.const.json'
    assert pnr_constraint_fn.exists()

    with pnr_constraint_fn.open("rt") as fp:
        pnr_constraints_d = json.load(fp=fp)

        min_layer_nm, max_layer_nm = None, None
        for const in pnr_constraints_d['constraints']:
            # use the last existing, non-None default
            if const['const_name'] == 'Route':
                if 'min_layer' in const:
                    min_layer_nm = const.get('min_layer')
                if 'max_layer' in const:
                    max_layer_nm = const.get('max_layer')


    DB.ExtractPinsToPowerPins(current_node)
    
    h_skip_factor = DB.getDrc_info().Design_info.h_skip_factor
    v_skip_factor = DB.getDrc_info().Design_info.v_skip_factor

    signal_routing_metal_l = DB.getDrc_info().Design_info.signal_routing_metal_l
    signal_routing_metal_u = DB.getDrc_info().Design_info.signal_routing_metal_u

    def convert_layer_to_int(nm, num):
        if nm is not None:
            if nm in DB.getDrc_info().Metalmap:
                return DB.getDrc_info().Metalmap[nm]
            else:
                logger.error(f"Metal layer '{nm}' not in Metalmap")
        return num

    signal_routing_metal_l = convert_layer_to_int(min_layer_nm, signal_routing_metal_l)
    signal_routing_metal_u = convert_layer_to_int(max_layer_nm, signal_routing_metal_u)

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

def router_driver(*, cap_map, cap_lef_s, 
                  numLayout, effort, adr_mode, PDN_mode,
                  router_mode, skipGDS, scale_factor,
                  nroutings, primitives, toplevel_args_d, results_dir, verilog_ds_to_run):

    fpath = toplevel_args_d['input_dir']
        
    res_dict = {}
    for concrete_top_name, scaled_placement_verilog_d in verilog_ds_to_run:

        connectivity_change_for_partial_routing(scaled_placement_verilog_d, primitives)

        tr_tbl = change_concrete_names_for_routing(scaled_placement_verilog_d)
        abstract_verilog_d = gen_abstract_verilog_d(scaled_placement_verilog_d)

        # don't need to send this to disk; for debug only
        if True:
            logger.debug(f"updated verilog: {abstract_verilog_d}")
            verilog_file = toplevel_args_d['verilog_file']

            abstract_verilog_file = verilog_file.replace(".verilog.json", ".abstract_verilog.json")

            with (pathlib.Path(fpath)/abstract_verilog_file).open("wt") as fp:
                json.dump(abstract_verilog_d.dict(), fp=fp, indent=2, default=str)
                
            scaled_placement_verilog_file = verilog_file.replace(".verilog.json", ".scaled_placement_verilog.json")

            with (pathlib.Path(fpath)/scaled_placement_verilog_file).open("wt") as fp:
                json.dump(scaled_placement_verilog_d.dict(), fp=fp, indent=2, default=str)


        lef_file = toplevel_args_d['lef_file']
        map_file = toplevel_args_d['map_file']
        new_lef_file = lef_file.replace(".placement_lef", ".lef")
        toplevel_args_d['lef_file'] = new_lef_file

        # Build up a new map file

        idir = pathlib.Path(fpath)
         
        cap_ctns = { str(pathlib.Path(gdsFile).stem) : gdsFile for atn, gdsFile in cap_map }

        map_d_in = []
        for leaf in scaled_placement_verilog_d['leaves']:
            ctn = leaf['concrete_name']
            if ctn in cap_ctns:
                map_d_in.append((ctn,cap_ctns[ctn]))
            elif (idir/f'{ctn}.json').exists():
                map_d_in.append((ctn,str(idir/f'{ctn}.gds')))
            else:
                logger.error(f'Missing .lef file for {ctn}')

        lef_s_in = None
        if cap_map:
            with (idir/new_lef_file).open("rt") as fp:
                lef_s_in = fp.read()
            lef_s_in += cap_lef_s


        # create a fresh DB and populate it with a placement verilog d    

        if router_mode in ['top_down', 'bottom_up']:
            DB, new_verilog_d, new_fpath, opath, _, _ = gen_DB_verilog_d(toplevel_args_d, results_dir, verilog_d_in=abstract_verilog_d, map_d_in=map_d_in, lef_s_in=lef_s_in)

            assert new_verilog_d == abstract_verilog_d

            assert new_fpath == fpath

            # populate new DB with placements to run

            hierarchical_place(DB=DB, opath=opath, fpath=fpath, numLayout=1, effort=effort,
                               verilog_d=abstract_verilog_d, lambda_coeff=1,
                               scale_factor=scale_factor,
                               placement_verilog_d=scaled_placement_verilog_d.dict(),
                               select_in_ILP=False, place_using_ILP=False, seed=0,
                               use_analytical_placer=False, ilp_solver='symphony',
                               primitives=primitives, placer_sa_iterations=10000, placer_ilp_runtime=1)

            placements_to_run = None

            res = route( DB=DB, idx=DB.TraverseHierTree()[-1], opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode,
                         router_mode=router_mode, skipGDS=skipGDS, placements_to_run=placements_to_run, nroutings=nroutings)

            res_dict.update(res)
    
        elif router_mode in ['collect_pins']:

            print(f'toplevel_args_d: {toplevel_args_d}')
            print(f'results_dir: {results_dir}')
            print(f'abstract_verilog_d: {abstract_verilog_d.json(indent=2)}')
            print(f'map_d_in: {map_d_in}')
            print(f'lef_s_in: {lef_s_in}')

            print(f'scaled_placement_verilog_d: {scaled_placement_verilog_d.json(indent=2)}')

            collect_pins(map_d_in, scaled_placement_verilog_d, toplevel_args_d)


    return res_dict

