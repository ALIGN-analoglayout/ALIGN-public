import logging
import pathlib
import json
import copy
from itertools import chain

from .. import PnR
from .render_placement import gen_placement_verilog, gen_boxes_and_hovertext
from .build_pnr_model import *
from .checker import check_placement
from ..gui.mockup import run_gui

logger = logging.getLogger(__name__)

Omark = PnR.Omark
TransformType = PnR.TransformType

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
            DB.PrintHierNode(current_node)
        else:
            current_node_copy = PnR.hierNode(current_node)
            DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
            return_name = f'{current_node_copy.name}_{current_node_copy.n_copy}_{lidx}' if return_name is None else return_name
            DB.WriteJSON(current_node_copy, True, True, True, True, return_name, drcInfo, opath)
            current_node.gdsFile = current_node_copy.gdsFile
            logger.info( f'SMB {current_node_copy.gdsFile}')
            DB.WriteLef(current_node_copy, f'{return_name}.lef', opath)
            DB.PrintHierNode(current_node_copy)
    else:
        if current_node.isTop:
            return_name = f'{current_node.name}_{lidx}' if return_name is None else return_name
        else:
            return_name = f'{current_node.name}_{current_node.n_copy}_{lidx}' if return_name is None else return_name
            current_node.gdsFile = f'{opath}{return_name}.gds'

    return return_name

def route_bottom_up( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS):

    # Compute all the needed subblocks
    subblocks_d = defaultdict(set)

    def aux(idx, sel):
        subblocks_d[idx].add(sel)
        current_node = DB.CheckoutHierNode(idx, sel) # Make a copy
        for blk in current_node.Blocks:
            child_idx = blk.child
            if child_idx >= 0:
                aux(child_idx, blk.selectedInstance)

    for lidx in range(DB.hierTree[idx].numPlacement):
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

            results_name_map[result_name] = ( (f'{current_node.name}:placement_{j}',), new_currentnode_idx_d[i][j])

            for blk in current_node.Blocks:
                if blk.child >= 0:
                    # Potential slug bug; uniqifying the vector each time
                    DB.hierTree[blk.child].parent = list(set(DB.hierTree[blk.child].parent + [ new_currentnode_idx_d[i][j] ]))
                    logger.debug( f'Set parent of {blk.child} to {DB.hierTree[blk.child].parent}')

    return results_name_map

def route_no_op( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS):
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

    results_name_map[result_name] = hierarchical_path

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

    results_name_map[result_name] = ( hierarchical_path, new_currentnode_idx)


    for blk in current_node.Blocks:
        if blk.child == -1: continue
        # Set the whole array, not parent[0]; otherwise the python temporary is updated
        DB.hierTree[blk.child].parent = [ new_currentnode_idx ]
        logger.debug( f'Set parent of {blk.child} to {new_currentnode_idx} => DB.hierTree[blk.child].parent[0]={DB.hierTree[blk.child].parent[0]}')

    logger.debug( f'End of route_top_down; placement idx {idx} lidx {lidx} nm {current_node.name} i_copy {i_copy} new_currentnode_idx {new_currentnode_idx}')

    return new_currentnode_idx

def route_top_down( *, DB, idx, opath, adr_mode, PDN_mode, skipGDS):
    assert len(DB.hierTree[idx].PnRAS) == DB.hierTree[idx].numPlacement

    results_name_map = {}
    new_topnode_indices = []
    for lidx in range(DB.hierTree[idx].numPlacement):
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


def place( *, DB, opath, fpath, numLayout, effort, idx, lambda_coeff):
    logger.info(f'Starting bottom-up placement on {DB.hierTree[idx].name} {idx}')

    current_node = DB.CheckoutHierNode(idx,-1)

    DB.AddingPowerPins(current_node)

    PRC = PnR.Placer_Router_Cap_Ifc(opath,fpath,current_node,DB.getDrc_info(),DB.checkoutSingleLEF(),1,6)

    hyper = PnR.PlacerHyperparameters()
    # Defaults; change (and uncomment) as required
    #hyper.T_INT = 1e6
    #hyper.T_MIN = 1e-6
    #hyper.ALPHA = 0.995
    #hyper.COUNT_LIMIT = 200
    hyper.LAMBDA = lambda_coeff

    curr_plc = PnR.PlacerIfc( current_node, numLayout, opath, effort, DB.getDrc_info(), hyper)

    actualNumLayout = curr_plc.getNodeVecSize()

    if actualNumLayout != numLayout:
        logger.warning( f'Placer did not provide numLayout ({numLayout} > {actualNumLayout}) layouts')

    for lidx in range(actualNumLayout):
        node = curr_plc.getNode(lidx)
        if node.Guardring_Consts:
            logger.info( f'Running guardring flow')
            PnR.GuardRingIfc( node, DB.checkoutSingleLEF(), DB.getDrc_info(), fpath)
        DB.Extract_RemovePowerPins(node)
        DB.CheckinHierNode(idx, node)

    DB.hierTree[idx].numPlacement = actualNumLayout

def route( *, DB, idx, opath, adr_mode, PDN_mode, router_mode, skipGDS):
    logger.info(f'Starting {router_mode} routing on {DB.hierTree[idx].name} {idx}')

    router_engines = { 'top_down': route_top_down,
                       'bottom_up': route_bottom_up,
                       'no_op': route_no_op
                       }

    return router_engines[router_mode]( DB=DB, idx=idx, opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode, skipGDS=skipGDS)

def subset_verilog_d( verilog_d, nm):
    # Should be an abstract verilog_d; no concrete_instance_names

    for module in verilog_d['modules']:
        for instance in module['instances']:
            assert 'concrete_template_name' not in instance
            assert 'abstract_template_name' in instance

    modules = { module['name'] : module for module in verilog_d['modules']}

    found_modules = set()
    def aux( module_name):
        found_modules.add( module_name)
        if module_name in modules:
            for instance in modules[module_name]['instances']:        
                atn = instance['abstract_template_name']
                aux( atn)

    aux(nm)

    new_verilog_d = copy.deepcopy(verilog_d)

    new_modules = []
    for module in new_verilog_d['modules']:
        if module['name'] in found_modules:
            new_modules.append( module)
    
    new_verilog_d['modules'] = new_modules

    return new_verilog_d


def place_and_route( *, DB, opath, fpath, numLayout, effort, adr_mode, PDN_mode, verilog_d, router_mode, gui, skipGDS, lambda_coeff):
    TraverseOrder = DB.TraverseHierTree()

    for idx in TraverseOrder:
        place( DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort, idx=idx, lambda_coeff=lambda_coeff)

    if verilog_d is not None:
        def r2wh( r):
            return (r[2]-r[0], r[3]-r[1])

        def gen_leaf_bbox_and_hovertext( ctn, p):
            #return (p, list(gen_boxes_and_hovertext( placement_verilog_d, ctn)))
            d = { 'width': p[0], 'height': p[1]}
            return (d, [ ((0, 0)+p, f'{ctn}<br>{0} {0} {p[0]} {p[1]}', True, 0)])

        leaf_map = defaultdict(dict)

        # Get all the leaf cells sizes; still doesn't get the CC capacitors
        for atn, gds_lst in DB.gdsData2.items():
            ctns = [str(pathlib.Path(fn).stem) for fn in gds_lst]
            for ctn in ctns:
                if ctn in DB.lefData:
                    lef = DB.lefData[ctn][0]
                    p = lef.width, lef.height
                    if ctn in leaf_map[atn]:
                        assert leaf_map[atn][ctn][0] == p
                    else:
                        leaf_map[atn][ctn] = gen_leaf_bbox_and_hovertext( ctn, p)

                else:
                    logger.error( f'LEF for concrete name {ctn} (of {atn}) missing.')


        tagged_bboxes = defaultdict(dict)
        for idx in TraverseOrder:
            nm = DB.hierTree[idx].name

            # Restrict verilog_d to include only sub-hierachies of nm
            s_verilog_d = subset_verilog_d( verilog_d, nm)

            for sel in range(DB.hierTree[idx].numPlacement):

                logger.debug( f'DB.CheckoutHierNode( {idx}, {sel})')
                hN = DB.CheckoutHierNode( idx, sel)

                # create new verilog for each placement
                placement_verilog_d = gen_placement_verilog( hN, DB, s_verilog_d)

                #(pathlib.Path(opath) / f'{nm}_{sel}.placement_verilog.json').write_text(placement_verilog_d.json(indent=2))

                check_placement(placement_verilog_d)

                if gui:
                    modules = { x['name']: x for x in placement_verilog_d['modules']}

                    p = r2wh(modules[nm]['bbox'])
                    d = { 'width': p[0], 'height': p[1],
                          'hpwl': hN.HPWL, 'cost': hN.cost,
                          'constraint_penalty': hN.constraint_penalty,
                          'area_norm': hN.area_norm, 'hpwl_norm': hN.HPWL_norm,
                          'area_scale': hN.area_norm/(p[0]*p[1]), 'hpwl_scale': hN.HPWL_norm/hN.HPWL
                    }
                    logger.info( f"data: {d}")

                    tagged_bboxes[nm][f'{nm}_{sel}'] = d, list(gen_boxes_and_hovertext( placement_verilog_d, nm))

                    leaves  = { x['name']: x for x in placement_verilog_d['leaves']}

                    # construct set of abstract_template_names
                    atns = defaultdict(set)

                    for module in placement_verilog_d['modules']:
                        for instance in module['instances']:
                            if 'abstract_template_name' in instance:
                                atn = instance['abstract_template_name'] 
                                if 'concrete_template_name' in instance:
                                    ctn = instance['concrete_template_name']
                                    atns[atn].add((ctn, r2wh(leaves[ctn]['bbox'])))

                    # Hack to get CC capacitors because they are missing from gdsData2 above
                    # Can be removed when CC capacitor generation is moved to correct spot in flow
                    for atn, v in atns.items():
                        for (ctn, p) in v:
                            if ctn in leaf_map[atn]:
                                assert leaf_map[atn][ctn][0] == { 'width': p[0], 'height': p[1]}
                            else:
                                leaf_map[atn][ctn] = gen_leaf_bbox_and_hovertext( ctn, p)

        if gui:
            tagged_bboxes.update( leaf_map)
            top_level = DB.hierTree[TraverseOrder[-1]].name
            run_gui( tagged_bboxes=tagged_bboxes, module_name=top_level, lambda_coeff=lambda_coeff)

    return route( DB=DB, idx=idx, opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode, router_mode=router_mode, skipGDS=skipGDS)

def toplevel(args, *, PDN_mode=False, adr_mode=False, results_dir=None, router_mode='top_down', gui=False, skipGDS=False, lambda_coeff):

    assert len(args) == 9

    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]

    DB, verilog_d = PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)

    if results_dir is None:
        opath = './Results/'
    else:
        opath = str(pathlib.Path(results_dir))
        if opath[-1] != '/':
            opath = opath + '/'

    pathlib.Path(opath).mkdir(parents=True,exist_ok=True)

    results_name_map = place_and_route( DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort, adr_mode=adr_mode, PDN_mode=PDN_mode, verilog_d=verilog_d, router_mode=router_mode, gui=gui, skipGDS=skipGDS, lambda_coeff=lambda_coeff)

    return DB, results_name_map
