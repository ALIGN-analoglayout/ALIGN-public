import logging
import re
import pathlib
import json
import copy
from collections import defaultdict
from .. import PnR
from .render_placement import gen_placement_verilog, scale_placement_verilog, gen_boxes_and_hovertext, standalone_overlap_checker, scalar_rational_scaling, round_to_angstroms
from .checker import check_placement, check_place_on_grid
from ..gui.mockup import run_gui
from .hpwl import calculate_HPWL_from_placement_verilog_d, gen_netlist
from .grid_constraints import gen_constraints
import math
from .build_pnr_model import gen_DB_verilog_d


logger = logging.getLogger(__name__)


PLACER_SA_MAX_ITER = 1e4


def place( *, DB, opath, fpath, numLayout, effort, idx, lambda_coeff, select_in_ILP, place_using_ILP, seed, use_analytical_placer, modules_d=None, ilp_solver, place_on_grid_constraints_json):

    logger.debug(f'Starting bottom-up placement on {DB.hierTree[idx].name} {idx}')

    current_node = DB.CheckoutHierNode(idx,-1)

    DB.AddingPowerPins(current_node)

    hyper = PnR.PlacerHyperparameters()
    # Defaults; change (and uncomment) as required
    hyper.T_INT = 0.5  # Increase for denormalized decision criteria
    hyper.T_MIN = 0.05
    hyper.ALPHA = math.exp(math.log(hyper.T_MIN/hyper.T_INT)/PLACER_SA_MAX_ITER)
    # hyper.T_MIN = hyper.T_INT*(hyper.ALPHA**1e4)    # 10k iterations
    # hyper.ALPHA = 0.99925
    # hyper.max_init_trial_count = 10000
    # hyper.max_cache_hit_count = 10
    hyper.SEED = seed  # if seed==0, C++ code will use its default value. Else, C++ code will use the provided value.
    # hyper.COUNT_LIMIT = 200
    hyper.select_in_ILP = select_in_ILP
    hyper.ilp_solver = 0 if ilp_solver == 'symphony' else 1
    hyper.LAMBDA = lambda_coeff
    hyper.use_analytical_placer = use_analytical_placer
    hyper.use_ILP_placer = place_using_ILP

    hyper.place_on_grid_constraints_json = place_on_grid_constraints_json

    if modules_d is not None:
        hyper.use_external_placement_info = True
        hyper.placement_info_json = json.dumps(modules_d, indent=2)

    curr_plc = PnR.PlacerIfc( current_node, numLayout, opath, effort, DB.getDrc_info(), hyper)

    actualNumLayout = curr_plc.getNodeVecSize()

    if actualNumLayout != numLayout:
        logger.debug( f'Placer did not provide numLayout ({numLayout} > {actualNumLayout}) layouts for {DB.hierTree[idx].name}')

    for lidx in range(actualNumLayout):
        node = curr_plc.getNode(lidx)
        if node.Guardring_Consts:
            logger.info( f'Running guardring flow')
            PnR.GuardRingIfc( node, DB.checkoutSingleLEF(), DB.getDrc_info(), fpath)
        DB.Extract_RemovePowerPins(node)
        DB.CheckinHierNode(idx, node)

    DB.hierTree[idx].numPlacement = actualNumLayout

def subset_verilog_d( verilog_d, nm):
    # Should be an abstract verilog_d; no concrete_instance_names

    for module in verilog_d['modules']:
        for instance in module['instances']:
            assert 'concrete_template_name' not in instance, (instance, module)
            assert 'abstract_template_name' in instance, (instance, module)

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

def gen_leaf_bbox_and_hovertext( ctn, p):
    #return (p, list(gen_boxes_and_hovertext( placement_verilog_d, ctn)))
    d = { 'width': p[0], 'height': p[1]}
    return d, [ ((0, 0)+p, f'{ctn}<br>{0} {0} {p[0]} {p[1]}', True, 0, False)], None

def scale_and_check_placement(*, placement_verilog_d, concrete_name, scale_factor, opath, placement_verilog_alternatives, is_toplevel):
    scaled_placement_verilog_d = scale_placement_verilog(placement_verilog_d, scale_factor)
    (pathlib.Path(opath) / f'{concrete_name}.scaled_placement_verilog.json').write_text(scaled_placement_verilog_d.json(indent=2,sort_keys=True))
    standalone_overlap_checker( scaled_placement_verilog_d, concrete_name)
    #Comment out the next two calls to disable checking (possibly to use the GUI to visualize the error.)
    check_placement( scaled_placement_verilog_d, scale_factor)
    if is_toplevel:
        check_place_on_grid(scaled_placement_verilog_d, concrete_name, opath)
    placement_verilog_alternatives[concrete_name] = scaled_placement_verilog_d

def per_placement( placement_verilog_d, *, hN, scale_factor, opath, placement_verilog_alternatives, is_toplevel, metrics):
    assert hN is not None
    abstract_name = hN.name
    concrete_names = { m['concrete_name'] for m in placement_verilog_d['modules'] if m['abstract_name'] == abstract_name}
    assert len(concrete_names) == 1, concrete_names
    concrete_name = next(iter(concrete_names))

    scale_and_check_placement( placement_verilog_d=placement_verilog_d, concrete_name=concrete_name, scale_factor=scale_factor, opath=opath, placement_verilog_alternatives=placement_verilog_alternatives, is_toplevel=is_toplevel)
    

    nets_d = gen_netlist( placement_verilog_d, concrete_name)
    hpwl_alt = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, concrete_name, nets_d, skip_globals=True)

    if hpwl_alt != hN.HPWL_extend:
        logger.warning( f'hpwl: locally computed from netlist {hpwl_alt}, placer computed {hN.HPWL_extend} differ!')
    else:
        logger.debug( f'hpwl: locally computed from netlist {hpwl_alt}, placer computed {hN.HPWL_extend} are equal!')

    reported_hpwl = hpwl_alt / 2000

    cost, constraint_penalty = hN.cost, hN.constraint_penalty
    area_norm, hpwl_norm = hN.area_norm, hN.HPWL_norm

    metrics[concrete_name] = {
        'hpwl': reported_hpwl, 'cost': cost,
        'constraint_penalty': constraint_penalty,
        'area_norm': area_norm, 'hpwl_norm': hpwl_norm,
        'abstract_name': abstract_name,
        'concrete_name': concrete_name
    }


def gen_leaf_map(*, DB):
    leaf_map = defaultdict(dict)

    # Get all the leaf cells sizes; now includes the CC capacitors
    for atn, gds_lst in DB.gdsData2.items():
        ctns = [str(pathlib.Path(fn).stem) for fn in gds_lst]
        for ctn in ctns:
            if ctn in DB.lefData:
                lef = DB.lefData[ctn][0]
                p = scalar_rational_scaling(lef.width,mul=0.001,div=2), scalar_rational_scaling(lef.height,mul=0.001,div=2)
                if ctn in leaf_map[atn]:
                    assert leaf_map[atn][ctn][0] == p, (leaf_map[atn][ctn][0], p)
                else:
                    leaf_map[atn][ctn] = gen_leaf_bbox_and_hovertext( ctn, p)

            else:
                logger.error( f'LEF for concrete name {ctn} (of {atn}) missing.')
    
    return leaf_map

def startup_gui(*, top_level, leaf_map, placement_verilog_alternatives, lambda_coeff, metrics):

    tagged_bboxes = defaultdict(dict)

    for concrete_name, placement_verilog_d in placement_verilog_alternatives.items():
        nets_d = gen_netlist(placement_verilog_d, concrete_name)

        def r2wh( r):
            return (round_to_angstroms(r[2]-r[0]), round_to_angstroms(r[3]-r[1]))

        # placement_verilog_d is in hN units
        # gui_scaled_placement_verilog_d is in microns
        gui_scaled_placement_verilog_d = scale_placement_verilog( placement_verilog_d, 0.001)

        modules = { x['concrete_name']: x for x in gui_scaled_placement_verilog_d['modules']}

        p = r2wh(modules[concrete_name]['bbox'])

        metrics[concrete_name].update( {'width': p[0], 'height': p[1]})

        abstract_name = metrics[concrete_name]['abstract_name']

        tagged_bboxes[abstract_name][concrete_name] = metrics[concrete_name], list(gen_boxes_and_hovertext( gui_scaled_placement_verilog_d, concrete_name, nets_d)), nets_d


    placements_to_run = None
    tagged_bboxes.update( leaf_map)

    print( f"Press Ctrl-C to end the GUI interaction. If current selection is a toplevel placement, the routing engine will be called on that placement. If the current selection is not toplevel (an intermediate hierarchy or a leaf), the router call will be skipped.")

    selected_concrete_name = run_gui( tagged_bboxes=tagged_bboxes, module_name=top_level, lambda_coeff=lambda_coeff)

    # Don't like name hacking; make we can do this another way
    p = re.compile( r'^(\S+)_(\d+)$')

    placements_to_run = []
    m = p.match(selected_concrete_name)
    if m:
        if m.groups()[0] == top_level:
            sel = int(m.groups()[1])
            placements_to_run = [sel]
    else:
        if selected_concrete_name in placement_verilog_alternatives:
            placements_to_run = None

    return placements_to_run



def process_placements(*, DB, verilog_d, lambda_coeff, scale_factor, opath):

    placement_verilog_alternatives = {}
    metrics = {}

    TraverseOrder = DB.TraverseHierTree()

    for idx in TraverseOrder:
        is_toplevel = idx == TraverseOrder[-1]

        # Restrict verilog_d to include only sub-hierachies of the current name
        s_verilog_d = subset_verilog_d( verilog_d, DB.hierTree[idx].name)

        for sel in range(DB.hierTree[idx].numPlacement):
            # create new verilog for each placement
            hN = DB.CheckoutHierNode( idx, sel)
            placement_verilog_d = gen_placement_verilog( hN, idx, sel, DB, s_verilog_d)
            per_placement( placement_verilog_d, hN=hN, scale_factor=scale_factor, opath=opath, placement_verilog_alternatives=placement_verilog_alternatives, is_toplevel=is_toplevel, metrics=metrics)

    leaf_map = gen_leaf_map(DB=DB)
    top_level = DB.hierTree[TraverseOrder[-1]].name

    del DB


    return top_level, leaf_map, placement_verilog_alternatives, metrics







def update_grid_constraints(grid_constraints, DB, idx, verilog_d, primitives, scale_factor):
    assert verilog_d is not None
    assert primitives is not None

    # for each layout, generate a placement_verilog_d, make sure the constraints are attached to the leaves, then generate the restrictions
    # convert the restrictions into the form needed for the subsequent placements

    # Restrict verilog_d to include only sub-hierachies of the current name
    s_verilog_d = subset_verilog_d( verilog_d, DB.hierTree[idx].name)

    frontier = {}

    for sel in range(DB.hierTree[idx].numPlacement):
        # create new verilog for each placement
        hN = DB.CheckoutHierNode( idx, sel)
        placement_verilog_d = gen_placement_verilog( hN, idx, sel, DB, s_verilog_d)
        # hN units
        scaled_placement_verilog_d = scale_placement_verilog( placement_verilog_d, scale_factor)
        # layers.json units (*5 if in anstroms)

        for leaf in scaled_placement_verilog_d['leaves']:
            ctn = leaf['concrete_name']
            if ctn not in primitives:
                continue # special case capacitors

            primitive = primitives[ctn]
            if 'metadata' in primitive and 'constraints' in primitive['metadata']:
                if 'constraints' not in leaf:
                    leaf['constraints'] = []

                leaf['constraints'].extend(constraint for constraint in primitive['metadata']['constraints'])

        top_name = f'{hN.name}_{sel}'
        gen_constraints(scaled_placement_verilog_d, top_name)
        top_module = next(iter([module for module in scaled_placement_verilog_d['modules'] if module['concrete_name'] == top_name]))

        frontier[top_name] = [constraint.dict() for constraint in top_module['constraints'] if constraint.constraint == 'place_on_grid']

        for constraint in frontier[top_name]:
            assert constraint['constraint'] == 'place_on_grid'
            # assert constraint['ored_terms'], f'No legal grid locations for {top_name} {constraint}'
            # Warn now and fail at the end for human-readable error message
            if not constraint['ored_terms']:
                logger.warning(f'No legal grid locations for {top_name} {constraint}')

    grid_constraints.update(frontier)


def hierarchical_place(*, DB, opath, fpath, numLayout, effort, verilog_d,
                       lambda_coeff, scale_factor,
                       placement_verilog_d, select_in_ILP, place_using_ILP, seed, use_analytical_placer, ilp_solver, primitives):

    logger.debug(f'Calling hierarchical_place with {"existing placement" if placement_verilog_d is not None else "no placement"}')

    if placement_verilog_d is not None:
        hack_placement_verilog_d = scale_placement_verilog( placement_verilog_d, scale_factor, invert=True)        

        modules = defaultdict(list)
        for m in hack_placement_verilog_d['modules']:
            modules[m['abstract_name']].append(m)

    grid_constraints = {}

    for idx in DB.TraverseHierTree():

        json_str = json.dumps([{'concrete_name': k, 'constraints': v} for k, v in grid_constraints.items()], indent=2)

        modules_d = None
        if placement_verilog_d is not None:
            modules_d = modules[DB.hierTree[idx].name]

        place(DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort, idx=idx,
              lambda_coeff=lambda_coeff, select_in_ILP=select_in_ILP, place_using_ILP=place_using_ILP,
              seed=seed, use_analytical_placer=use_analytical_placer,
              modules_d=modules_d, ilp_solver=ilp_solver, place_on_grid_constraints_json=json_str)

        update_grid_constraints(grid_constraints, DB, idx, verilog_d, primitives, scale_factor)


    top_level, leaf_map, placement_verilog_alternatives, metrics = process_placements(DB=DB, verilog_d=verilog_d,
                                                                                      lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                                                                      opath=opath)

    return top_level, leaf_map, placement_verilog_alternatives, metrics



def placer_driver(*, cap_map, cap_lef_s,
                  lambda_coeff, scale_factor,
                  select_in_ILP, place_using_ILP, seed,
                  use_analytical_placer, ilp_solver, primitives, toplevel_args_d, results_dir):

    fpath = toplevel_args_d['input_dir']

    idir = pathlib.Path(fpath)

    lef_file = toplevel_args_d['lef_file']
    map_file = toplevel_args_d['map_file']

    p = re.compile(r'^(\S+)\s+(\S+)\s*$')

    map_d_in = []
    with (idir/map_file).open("rt") as fp:
        for line in fp:
            line = line.rstrip('\n')
            m = p.match(line)
            assert m
            map_d_in.append(m.groups())

    lef_s_in = None
    if cap_map:
        map_d_in.extend(cap_map)

        with (idir/lef_file).open("rt") as fp:
            lef_s_in = fp.read()

        lef_s_in += cap_lef_s


    DB, verilog_d, new_fpath, opath, numLayout, effort = gen_DB_verilog_d(toplevel_args_d=toplevel_args_d, results_dir=results_dir, map_d_in=map_d_in, lef_s_in=lef_s_in)

    assert new_fpath == fpath

    logger.debug(f'Using {ilp_solver} to solve ILP in placer')

    top_level, leaf_map, placement_verilog_alternatives, metrics = hierarchical_place(DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort,
                                                                                      verilog_d=verilog_d, lambda_coeff=lambda_coeff,
                                                                                      scale_factor=scale_factor,
                                                                                      placement_verilog_d=None,
                                                                                      select_in_ILP=select_in_ILP, place_using_ILP=place_using_ILP, seed=seed,
                                                                                      use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver,
                                                                                      primitives=primitives)

    return top_level, leaf_map, placement_verilog_alternatives, metrics
