import logging
import pathlib
import json
from itertools import chain

from .. import PnR
from .render_placement import dump_blocks

logger = logging.getLogger(__name__)

NType = PnR.NType
Omark = PnR.Omark
TransformType = PnR.TransformType

def route_single_variant( DB, drcInfo, current_node, lidx, opath, binary_directory, adr_mode, *, PDN_mode, pdk):
    NEW_GLOBAL_ROUTER = True
    h_skip_factor = 5;
    v_skip_factor = 5;

    #logger.info( f"SMB {list(pdk['design_info'].keys())}")
    logger.info( f"SMB {list(pdk.keys())}")

    signal_routing_metal_l = 0;
    signal_routing_metal_u = 8;

    curr_route = PnR.Router()

    def RouteWork( mode, current_node, *, metal_l=signal_routing_metal_l, metal_u=signal_routing_metal_u, fn=''):
        curr_route.RouteWork( mode, current_node, drcInfo,
                              metal_l, metal_u,
                              binary_directory, h_skip_factor, v_skip_factor, fn)

    if NEW_GLOBAL_ROUTER:
        RouteWork( 6 if adr_mode else 4, current_node)

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
    else:
        # Global Routing (old version)
        RouteWork(0, current_node)

        DB.WriteJSON(current_node, True, True, False, False, f'{current_node.name}_GR_{lidx}', drcInfo, opath)

        # The following line is used to write global route results for Intel router (only for old version)
        DB.WriteGlobalRoute(current_node, f'{current_node.name}_GlobalRoute_{lidx}.json', opath)

        # Detail Routing
        RouteWork( 1, current_node)

    if current_node.isTop:
        DB.WriteJSON(current_node, True, True, False, False, f'{current_node.name}_DR_{lidx}', drcInfo, opath)
    else:
        current_node_copy = PnR.hierNode(current_node)
        DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
        DB.WriteJSON(current_node_copy, True, True, False, False,
                     f'{current_node_copy.name}_DR_{current_node_copy.n_copy}_{lidx}', drcInfo, opath)
        current_node.gdsFile = current_node_copy.gdsFile

    if current_node.isTop:
        power_grid_metal_l = 5
        power_grid_metal_u = 6
        power_routing_metal_l = 0
        power_routing_metal_u = 6

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

            power_grid_metal_l = 2
            power_grid_metal_u = 11
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

        DB.WriteJSON(current_node, True, True, False, True, f'{current_node.name}_PG_{lidx}', drcInfo, opath)

        logger.debug("Checkpoint : Starting Power Routing");

        RouteWork(3, current_node, metal_l=power_routing_metal_l, metal_u=power_routing_metal_u)

        DB.WriteJSON(current_node, True, False, True, True, f'{current_node.name}_PR_{lidx}', drcInfo, opath)

        DB.Write_Router_Report(current_node, opath)

    # transform current_node into current_node coordinate
    if current_node.isTop:
        DB.WriteJSON(current_node, True, True, True, True, f'{current_node.name}_{lidx}', drcInfo, opath)
        DB.WriteLef(current_node, f'{current_node.name}_{lidx}.lef', opath)
        DB.PrintHierNode(current_node)
    else:
        current_node_copy = PnR.hierNode(current_node)
        DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, TransformType.Backward)
        DB.WriteJSON(current_node_copy, True, True, True, True,
                     f'{current_node_copy.name}_{current_node_copy.n_copy}_{lidx}', drcInfo, opath)
        current_node.gdsFile = current_node_copy.gdsFile
        DB.WriteLef(current_node_copy,
                    f'{current_node_copy.name}_{current_node_copy.n_copy}_{lidx}.lef', opath)

        DB.PrintHierNode(current_node_copy)


def route_top_down( DB, drcInfo,
                    bounding_box,
                    current_node_ort, idx, lidx,
                    opath, binary_directory, adr_mode, *, PDN_mode, pdk):

    current_node = DB.CheckoutHierNode(idx) # Make a copy
    i_copy = DB.hierTree[idx].n_copy

    logger.debug( f'Start of route_top_down; placement idx {idx} lidx {lidx} nm {current_node.name} i_copy {i_copy}')
    

    DB.hierTree[idx].n_copy += 1
    current_node_name = current_node.name
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
        new_childnode_idx = route_top_down(DB, drcInfo, childnode_bbox, childnode_orient, child_idx, 0, opath, binary_directory, adr_mode, PDN_mode=PDN_mode, pdk=pdk)
        DB.CheckinChildnodetoBlock(current_node, bit, DB.hierTree[new_childnode_idx])
        current_node.Blocks[bit].child = new_childnode_idx

    DB.ExtractPinsToPowerPins(current_node)
    route_single_variant( DB, drcInfo, current_node, lidx, opath, binary_directory, adr_mode, PDN_mode=PDN_mode, pdk=pdk)

    if not current_node.isTop:
        DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, TransformType.Backward)

    logger.debug( f'Before DB.AppendToHierTree len(DB.hierTree)={len(DB.hierTree)}')
    DB.AppendToHierTree(current_node)
    logger.debug( f'After DB.AppendToHierTree len(DB.hierTree)={len(DB.hierTree)}')
    new_currentnode_idx = len(DB.hierTree) - 1

    for bit,blk in enumerate(current_node.Blocks):
        if blk.child == -1: continue
        DB.SetParentInHierTree( blk.child, 0, new_currentnode_idx)
        logger.debug( f'Set parent of {blk.child} to {new_currentnode_idx} => DB.hierTree[blk.child].parent[0]={DB.hierTree[blk.child].parent[0]}')

    logger.debug( f'End of route_top_down; placement idx {idx} lidx {lidx} nm {current_node.name} i_copy {i_copy} new_currentnode_idx {new_currentnode_idx}')

    return new_currentnode_idx


def analyze_hN( tag, hN, beforeAddingBlockPins=False):
    logger.info( f'{tag} name {hN.name}')

    logger.info( f'Nets and PowerNets')
    for net in chain( hN.Nets, hN.PowerNets):
        logger.info( f'  {net.name}')
        for conn in net.connected:
            if conn.type == NType.Block:
                if 0 <= conn.iter2 < len(hN.Blocks):
                    blk = hN.Blocks[conn.iter2]
                    inst = blk.instance[0]

                    if 0 <= conn.iter < len(inst.blockPins):

                        logger.info( f'    {conn.type} {conn.iter} ({inst.blockPins[conn.iter].name}) {conn.iter2} ({inst.name} {inst.master})')
                    else:
                        logger.info( f'    {conn.type} {conn.iter} (<out of range>) {conn.iter2} ({inst.name} {inst.master})')                        

                else:
                    logger.info( f'    {conn.type} {conn.iter} (<unknown>) {conn.iter2} (<out of range>)')
            elif conn.type == NType.Terminal:
                assert conn.iter2 == -1
                if 0 <= conn.iter < len(hN.Terminals):
                    logger.info( f'    {conn.type} {conn.iter} ({hN.Terminals[conn.iter].name})')
                else:
                    logger.info( f'    {conn.type} {conn.iter} (<out of range>)')

    logger.info( f'PowerNets (second pass)')
    for net in hN.PowerNets:
        logger.info( f'  {net.name}')
        for conn in net.dummy_connected:
            if 0 <= conn.iter2 < len(hN.Blocks):
                blk = hN.Blocks[conn.iter2]
                logger.info( f'    blk.selectedInstance={blk.selectedInstance}')
                for inst_idx,inst in enumerate(blk.instance):
                    if beforeAddingBlockPins:
                        if 0 <= conn.iter < len(inst.dummy_power_pin):
                            logger.info( f'    {conn.iter} ({inst.dummy_power_pin[conn.iter].name}) {conn.iter2} ({inst.name} {inst.master}) inst_idx={inst_idx}')
                        else:
                            logger.info( f'    {conn.iter} (<out of range>) {conn.iter2} ({inst.name} {inst.master}) inst_idx={inst_idx}')                        
            else:
                logger.info( f'    {conn.iter} (<unknown>) {conn.iter2} (<out of range>)')

    logger.info( f'Blocks')
    for blk in hN.Blocks:
        logger.info( f'  blk.child={blk.child} len(blk.instance)={len(blk.instance)} blk.selectedInstance={blk.selectedInstance} blk.instNum={blk.instNum}')
        for inst in blk.instance:
            logger.info( f'    inst.name={inst.name} inst.master={inst.master} len(inst.dummy_power_pin)={len(inst.dummy_power_pin)}')


def toplevel(args, *, PDN_mode=False, pdk=None, render_placements=False):

    assert len(args) == 9

    adr_mode = False

    opath = './Results/'
    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]
    if opath[-1] != '/': opath += '/'

    # find directory that args[0] sits in
    binary_directory = str(pathlib.Path(args[0]).parent)

    pathlib.Path(opath).mkdir(parents=True,exist_ok=True)

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)
    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()

    TraverseOrder = DB.TraverseHierTree()

    for idx in TraverseOrder:
        logger.info(f'Topo order: {idx} {DB.hierTree[idx].name}')

        current_node = DB.CheckoutHierNode(idx)
        #analyze_hN( 'Start', current_node, True)

        DB.AddingPowerPins(current_node)
        #analyze_hN( 'After adding power pins', current_node, False)

        PRC = PnR.Placer_Router_Cap_Ifc(opath,fpath,current_node,drcInfo,lefData,1,6)

        curr_plc = PnR.PlacerIfc( current_node, numLayout, opath, effort, drcInfo)

        actualNumLayout = curr_plc.getNodeVecSize()
        
        if actualNumLayout != numLayout:
            logger.warning( f'Placer did not provide numLayout ({numLayout} > {actualNumLayout}) layouts')

        for lidx in range(actualNumLayout):
            node = curr_plc.getNode(lidx)
            if node.Guardring_Consts:
                PnR.GuardRingIfc( node, lefData, drcInfo)
            #analyze_hN( f'After placement {lidx}', node, False)
            DB.Extract_RemovePowerPins(node)
            #analyze_hN( f'After remove power pins {lidx}', node, True)
            DB.CheckinHierNode(idx, node)

        DB.hierTree[idx].numPlacement = actualNumLayout
        #analyze_hN( 'End', current_node, False)

    if render_placements:
        dump_blocks( DB.hierTree[TraverseOrder[-1]], DB, leaves_only=False)

    logger.debug(f'Starting top-down routing')

    last = TraverseOrder[-1]
    new_topnode_indices = []

    assert len(DB.hierTree[last].PnRAS) == DB.hierTree[last].numPlacement

    for lidx in range(DB.hierTree[last].numPlacement):
        new_topnode_idx = route_top_down( DB, drcInfo,
                                          PnR.bbox( PnR.point(0,0),
                                                    PnR.point(DB.hierTree[last].PnRAS[lidx].width,
                                                              DB.hierTree[last].PnRAS[lidx].height)),
                                          Omark.N, last, lidx,
                                          opath, binary_directory, adr_mode, PDN_mode=PDN_mode, pdk=pdk)
        new_topnode_indices.append(new_topnode_idx)

    return DB
