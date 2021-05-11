import pathlib
import shutil
import os
import json
import re
import copy
import math
from collections import defaultdict

from .compiler import generate_hierarchy
from .primitive import generate_primitive
from .pnr import generate_pnr
from .gdsconv.json2gds import convert_GDSjson_GDS
from .utils.gds2png import generate_png
from .utils.logging import reconfigure_loglevels

import logging
logger = logging.getLogger(__name__)

def build_steps( flow_start, flow_stop):
    steps = [ '1_topology', '2_primitives', '3_pnr']

    start_idx = 0
    if flow_start is not None:
        assert flow_start in steps
        start_idx = steps.index( flow_start)
    stop_idx = len(steps)
    if flow_stop is not None:
        assert flow_stop in steps
        stop_idx = steps.index( flow_stop)+1

    assert start_idx < stop_idx, f'No steps to run in the flow: {steps}[{start_idx}:{stop_idx}]'

    steps_to_run = steps[start_idx:stop_idx]
    logger.info( f'Steps to run in the flow: {steps}[{start_idx}:{stop_idx}] => {steps_to_run}')

    return steps_to_run


def gen_more_primitives( primitives, topology_dir, subckt):
    """primitives dictionary updated in place"""

    #
    # This code should be improved at moved to 2_primitives
    #
    map_d = defaultdict(list)

    # As a hack, add more primitives if it matches this pattern
    p = re.compile( r'^(\S+)_nfin(\d+)_n(\d+)_X(\d+)_Y(\d+)(|_\S+)$')

    more_primitives = {}

    for k,v in primitives.items():
        m = p.match(k)
        if m:
            logger.info( f'Matched primitive {k}')
            nfin,n,X,Y = tuple(int(x) for x in m.groups()[1:5])
            abstract_name = f'{m.groups()[0]}_nfin{nfin}{m.groups()[5]}'

            map_d[abstract_name].append( k)

            clusters = (nfin+n-1) // n

            pairs = set()
            for newx in range( 1, clusters+1):
                newy = (nfin+newx*n-1)//(newx*n)
                assert newx*newy*n >= nfin
                pairs.add( (newx,newy))

            by_y = defaultdict(list)
            for x,y in pairs:
                by_y[y].append( x)

            pairs = set()
            for y,xs in by_y.items():
                pairs.add( (min(xs), y))

            pairs = pairs.difference( { (X,Y)})

            #
            # Hack to limit aspect ratios when there are a lot of choices
            #
            if len(pairs) > 12:
                new_pairs = []
                #log10_aspect_ratios = [ -1.0, -0.3, -0.1, 0, 0.1, 0.3, 1.0]
                log10_aspect_ratios = [ -0.3, 0, 0.3]
                for l in log10_aspect_ratios:
                    best_pair = min( (abs( math.log10(newy) - math.log10(newx) - l), (newx, newy)) for newx,newy in pairs)[1]
                    new_pairs.append( best_pair)
                pairs = new_pairs

            logger.info( f'Inject new primitive sizes: {pairs} for {nfin} {n} {X} {Y}')

            for newx,newy in pairs:
                concrete_name = f'{m.groups()[0]}_nfin{nfin}_n{n}_X{newx}_Y{newy}{m.groups()[5]}'
                map_d[abstract_name].append( concrete_name)             
                if concrete_name not in primitives and \
                   concrete_name not in more_primitives:
                    more_primitives[concrete_name] = copy.deepcopy(v)
                    more_primitives[concrete_name]['x_cells'] = newx
                    more_primitives[concrete_name]['y_cells'] = newy
        else:
            if not (k.startswith( "Res") or k.startswith( "Cap")): 
                logger.warning( f'Didn\'t match primitive {k}')
            map_d[k].append( k)

    #SMB Hack to see if this is causing trouble with bottom up
    #primitives.update( more_primitives)

    #
    # This code should move to 1_topology, we also need two different the primitives.json files;
    # One generated in 1_topology and consumed by 2_primitives that has abstract_template_names
    # One generated in 2_primitives and consumed by 3_pnr that has both abstract_template_names and concrete_template_name
    #
    concrete2abstract = { vv:k for k,v in map_d.items() for vv in v}

    for k,v in primitives.items():
        v['abstract_template_name'] = concrete2abstract[k]
        v['concrete_template_name'] = k

    # now hack the netlist to replace the template names using the concrete2abstract mapping

    with (topology_dir / f'{subckt}.verilog.json').open( 'rt') as fp:
        verilog_json_d = json.load(fp)

    for module in verilog_json_d['modules']:
        for instance in module['instances']:
            t = instance['template_name'] 
            if t in concrete2abstract:
                del instance['template_name']
                instance['abstract_template_name'] = concrete2abstract[t]

    with (topology_dir / f'{subckt}.verilog.json').open( 'wt') as fp:
        json.dump( verilog_json_d, fp=fp, indent=2)


def schematic2layout(netlist_dir, pdk_dir, netlist_file=None, subckt=None, working_dir=None, flatten=False, unit_size_mos=10, unit_size_cap=10, nvariants=1, effort=0, extract=False, log_level=None, verbosity=None, generate=False, python_gds_json=True, regression=False, uniform_height=False, PDN_mode=False, flow_start=None, flow_stop=None, router_mode='top_down', gui=False):

    check = True 

    steps_to_run = build_steps( flow_start, flow_stop)

    reconfigure_loglevels(file_level=log_level, console_level=verbosity)

    if working_dir is None:
        working_dir = pathlib.Path.cwd().resolve()
    else:
        working_dir = pathlib.Path(working_dir).resolve()
    if not working_dir.is_dir():
        logger.error(f"Working directory {working_dir} doesn't exist. Please enter a valid directory path.")
        raise FileNotFoundError(2, 'No such working directory', working_dir)

    pdk_dir = pathlib.Path(pdk_dir).resolve()
    if not pdk_dir.is_dir():
        logger.error(f"PDK directory {pdk_dir} doesn't exist. Please enter a valid directory path")
        raise FileNotFoundError(2, 'No such pdk directory', pdk_dir)

    netlist_dir = pathlib.Path(netlist_dir).resolve()
    if not netlist_dir.is_dir():
        logger.error(f"Netlist directory {netlist_dir} doesn't exist. Please enter a valid directory path")
        raise FileNotFoundError(2, 'No such netlist directory', netlist_dir)

    netlist_files = [x for x in netlist_dir.iterdir() if x.is_file() and x.suffix in ('.sp', '.cdl')]
    if not netlist_files:
        logger.error(
            f"No spice files found in netlist directory {netlist_dir}. Exiting...")
        raise FileNotFoundError(2, 'No matching netlist files', f'{netlist_dir}/*(.sp|.cdl)')

    if netlist_file:
        netlist_file = pathlib.Path(netlist_file).resolve()
        netlist_files = [x for x in netlist_files if netlist_file == x]
        if not netlist_files:
            logger.error(
                f"No spice files {netlist_file} found in netlist directory. Exiting...")
            raise FileNotFoundError(2, 'No such netlist file', netlist_file)

    if subckt is None:
        assert len(netlist_files) == 1, "Encountered multiple spice files. Cannot infer top-level circuit"
        subckt = netlist_files[0].stem

    if regression:
        # Copy regression results in one dir
        regression_dir = working_dir / 'regression'
        regression_dir.mkdir(exist_ok=True)

    assert len(netlist_files) == 1, "Only one .sp file allowed"
    netlist = netlist_files[0]

    results = []

    logger.info(f"READ file: {netlist} subckt={subckt}, flat={flatten}")

    # Generate hierarchy
    topology_dir = working_dir / '1_topology'
    if '1_topology' in steps_to_run:
        topology_dir.mkdir(exist_ok=True)
        primitives = generate_hierarchy(netlist, subckt, topology_dir, flatten, pdk_dir, uniform_height)

        gen_more_primitives( primitives, topology_dir, subckt)

        with (topology_dir / 'primitives.json').open( 'wt') as fp:
            json.dump( primitives, fp=fp, indent=2)
    else:
        with (topology_dir / 'primitives.json').open( 'rt') as fp:
            primitives = json.load(fp)
        

    # Generate primitives
    primitive_dir = (working_dir / '2_primitives')
    if '2_primitives' in steps_to_run:
        primitive_dir.mkdir(exist_ok=True)
        for block_name, block_args in primitives.items():
            logger.debug(f"Generating primitive: {block_name}")
            generate_primitive(block_name, **block_args, pdkdir=pdk_dir, outputdir=primitive_dir)

    # run PNR tool
    pnr_dir = working_dir / '3_pnr'
    if '3_pnr' in steps_to_run:
        pnr_dir.mkdir(exist_ok=True)
        variants = generate_pnr(topology_dir, primitive_dir, pdk_dir, pnr_dir, subckt, primitives=primitives, nvariants=nvariants, effort=effort, check=check, extract=extract, gds_json=python_gds_json, PDN_mode=PDN_mode, router_mode=router_mode, gui=gui)
        results.append( (netlist, variants))
        assert router_mode == 'no_op' or len(variants) > 0, f"No layouts were generated for {netlist}. Cannot proceed further. See LOG/align.log for last error."

        # Generate necessary output collateral into current directory
        for variant, filemap in variants.items():
            convert_GDSjson_GDS(filemap['gdsjson'], working_dir / f'{variant}.gds')
            print("Use KLayout to visualize the generated GDS:",working_dir / f'{variant}.gds')

            if os.getenv('ALIGN_HOME', False):
                shutil.copy(pnr_dir/f'{variant}.json',
                            pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/f'{variant}.json')

            if 'python_gds_json' in filemap:
                convert_GDSjson_GDS(filemap['python_gds_json'], working_dir / f'{variant}.python.gds')
                print("Use KLayout to visualize the python generated GDS:",working_dir / f'{variant}.python.gds')


            (working_dir / filemap['lef'].name).write_text(filemap['lef'].read_text())
            if check:
                if filemap['errors'] > 0:
                    (working_dir / filemap['errfile'].name).write_text(filemap['errfile'].read_text())

            if extract:
                (working_dir / filemap['cir'].name).write_text(filemap['cir'].read_text())
            # Generate PNG
            if generate:
                generate_png(working_dir, variant)
            if regression:
                # Copy regression results in one dir
                (regression_dir / filemap['gdsjson'].name).write_text(filemap['gdsjson'].read_text())
                (regression_dir / filemap['python_gds_json'].name).write_text(filemap['python_gds_json'].read_text())
                convert_GDSjson_GDS(filemap['python_gds_json'], regression_dir / f'{variant}.python.gds')                
                convert_GDSjson_GDS(filemap['gdsjson'], regression_dir / f'{variant}.gds')
                (regression_dir / filemap['lef'].name).write_text(filemap['lef'].read_text())
                (regression_dir / f'{subckt}.v').write_text((topology_dir / f'{subckt}.v').read_text())
                for file_ in topology_dir.iterdir():
                    if file_.suffix == '.const':
                        (regression_dir / file_.name).write_text(file_.read_text())
    return results

