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
from .router import route

from .build_pnr_model import PnRdatabase, NType
from ..schema.hacks import List, FormalActualMap, VerilogJsonTop, VerilogJsonModule

logger = logging.getLogger(__name__)

# Doesn't seem to be used
def write_verilog_json(verilog_d):
    return {"modules":[{"name":m.name,
                        "parameters": list(m.parameters),
                        "constraints": [mc.dict() for mc in m.constraints],
                        "instances": [mi.dict() for mi in m.instances],
                        } for m in verilog_d.modules],
        "global_signals":verilog_d.global_signals}


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


def placer_driver(*, DB, opath, fpath, numLayout, effort, verilog_d,
                  gui, lambda_coeff, scale_factor,
                  reference_placement_verilog_json, concrete_top_name, select_in_ILP, seed,
                  use_analytical_placer, ilp_solver, primitives, nroutings, toplevel_args, results_dir):

    logger.debug(f'Using {ilp_solver} to solve ILP in placer')

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

    return verilog_ds_to_run


def router_driver(*, opath, fpath, numLayout, effort, adr_mode, PDN_mode,
                  router_mode, skipGDS, lambda_coeff, scale_factor,
                  reference_placement_verilog_json, concrete_top_name, nroutings,
                  primitives, toplevel_args, results_dir, verilog_ds_to_run):


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
                                                  select_in_ILP=False, seed=0,
                                                  use_analytical_placer=False, ilp_solver='symphony',
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

    verilog_ds_to_run = placer_driver(DB=DB, opath=opath, fpath=fpath, numLayout=numLayout, effort=effort, verilog_d=verilog_d,
                                      gui=gui, lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                      reference_placement_verilog_json=reference_placement_verilog_json, concrete_top_name=concrete_top_name, select_in_ILP=select_in_ILP, seed=seed,
                                      use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver, primitives=primitives, nroutings=nroutings,
                                      toplevel_args=args, results_dir=results_dir)

    res_dict = router_driver(opath=opath, fpath=fpath, numLayout=numLayout, effort=effort, adr_mode=adr_mode, PDN_mode=PDN_mode,
                             router_mode=router_mode, skipGDS=skipGDS, lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                             reference_placement_verilog_json=reference_placement_verilog_json, concrete_top_name=concrete_top_name, nroutings=nroutings,
                             primitives=primitives, toplevel_args=args, results_dir=results_dir,
                             verilog_ds_to_run=verilog_ds_to_run)


    return res_dict

def toplevel_route_only(args, *, PDN_mode=False, adr_mode=False, results_dir=None, router_mode='top_down',
                        gui=False, skipGDS=False,
                        nroutings=1, select_in_ILP=False,
                        seed=0, use_analytical_placer=False):

    DB, verilog_d, fpath, opath, numLayout, effort = gen_DB_verilog_d(args)

    idx = 0
    results_name_map = route( DB=DB, idx=idx, opath=opath, adr_mode=adr_mode, PDN_mode=PDN_mode,
                              router_mode=router_mode, skipGDS=skipGDS, placements_to_run=None, nroutings=nroutings)

    return results_name_map
