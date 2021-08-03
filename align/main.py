import pathlib
import shutil
import os
import json
import re
import copy
import math
from collections import defaultdict
import sys
import http.server
import socketserver
import functools

from .compiler import generate_hierarchy
from .primitive import generate_primitive
from .pnr import generate_pnr
from .gdsconv.json2gds import convert_GDSjson_GDS
from .utils.gds2png import generate_png
from .utils import logmanager

import logging
logger = logging.getLogger(__name__)

def build_steps( flow_start, flow_stop):
    steps = [ '1_topology', '2_primitives', '3_pnr']
    sub_steps = { '3_pnr': ['prep', 'place', 'route', 'check']}

    unimplemented_start_points = { '3_pnr:route', '3_pnr:check'}
    unimplemented_stop_points = { '3_pnr:place'}

    if flow_start is None:
        flow_start = steps[0]
    if flow_start in unimplemented_start_points:
        raise NotImplementedError(f'Don\'t know how to start from {flow_start}')
    start_t = tuple(flow_start.split(':')) if ':' in flow_start else (flow_start,)

    if flow_stop is None:
        flow_stop = steps[-1]
    if flow_stop in unimplemented_stop_points:
        raise NotImplementedError(f'Don\'t know how to stop at {flow_stop}')
    stop_t = tuple(flow_stop.split(':')) if ':' in flow_stop else (flow_stop,)

    steps_to_run = []
    enabled = False
    for step in steps:
        if (step,) == start_t: enabled = True
        if step in sub_steps:
            for sub_step in sub_steps[step]:
                if (step,sub_step) == start_t: enabled = True
                if enabled: steps_to_run.append( f'{step}:{sub_step}')
                if (step,sub_step) == stop_t:
                    assert enabled, f'Stopping flow before it started: {flow_start} {flow_stop}'
                    enabled = False
        else:
            if enabled: steps_to_run.append( f'{step}')
            if (step,) == stop_t:
                assert enabled, f'Stopping flow before it started: {flow_start} {flow_stop}'
                enabled = False

    logger.info( f'Running flow steps {steps_to_run}')

    return steps_to_run


def gen_more_primitives( primitives, topology_dir, subckt):
    """primitives dictionary updated in place"""

    #
    # This code should be improved and moved to 2_primitives
    #
    map_d = defaultdict(list)

    # As a hack, add more primitives if it matches this pattern
    p = re.compile( r'^(\S+)_nfin(\d+)_n(\d+)_X(\d+)_Y(\d+)(|_\S+)$')

    p_2 = re.compile( r'^(\S+)_x(\d+)_y(\d+)$')

    more_primitives = {}

    #
    # Hack to limit aspect ratios when there are a lot of choices
    #
    def limit_pairs( pairs):
        if len(pairs) > 12:
            new_pairs = []
            #log10_aspect_ratios = [ -1.0, -0.3, -0.1, 0, 0.1, 0.3, 1.0]
            log10_aspect_ratios = [ -0.3, 0, 0.3]
            for l in log10_aspect_ratios:
                best_pair = min( (abs( math.log10(newy) - math.log10(newx) - l), (newx, newy))
                                 for newx,newy in pairs)[1]
                new_pairs.append( best_pair)
            return new_pairs
        else:
            return pairs

    def gen_pairs( n, nfin):
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

        return limit_pairs( pairs.difference( { (X,Y)}))

    for k,v in primitives.items():

        m = p.match(k)
        mm = p_2.match(k)

        if m:
            nfin,n,X,Y = tuple(int(x) for x in m.groups()[1:-1])
            prefix = f'{m.groups()[0]}_nfin{nfin}'
            suffix = m.groups()[-1]
            pairs = gen_pairs( n, nfin)

            abstract_name = f'{prefix}{suffix}'
            map_d[abstract_name].append( k)
            for newx,newy in pairs:
                concrete_name = f'{prefix}_n{n}_X{newx}_Y{newy}{suffix}'
                map_d[abstract_name].append( concrete_name)             
                if concrete_name not in primitives and \
                   concrete_name not in more_primitives:
                    more_primitives[concrete_name] = copy.deepcopy(v)
                    more_primitives[concrete_name]['x_cells'] = newx
                    more_primitives[concrete_name]['y_cells'] = newy

        elif mm:
            prefix = mm.groups()[0]
            x, y = tuple(int(x) for x in mm.groups()[1:])
            prefix = mm.groups()[0]
            pairs = set()
            m = x*y
            y_sqrt = math.floor(math.sqrt(x*y))
            for y in range(y_sqrt, 0, -1):
                if m % y == 0:
                    pairs.add((y, m//y))
                    pairs.add((m//y, y))
                if y == 1:
                    break

            pairs = limit_pairs(pairs)

            abstract_name = f'{prefix}'
            map_d[abstract_name].append(k)
            for newx,newy in pairs:
                concrete_name = f'{prefix}_x{newx}_y{newy}'
                map_d[abstract_name].append( concrete_name)             
                if concrete_name not in primitives and concrete_name not in more_primitives:
                    more_primitives[concrete_name] = copy.deepcopy(v)
                    more_primitives[concrete_name]['x_cells'] = newx
                    more_primitives[concrete_name]['y_cells'] = newy

        else:
            if not (k.startswith( "Res") or k.startswith( "Cap")): 
                logger.warning( f'Didn\'t match primitive {k}')
            map_d[k].append( k)

    primitives.update( more_primitives)

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
            else:
                # actually want all instances to use abstract_template_name, even the non-leaf ones
                del instance['template_name']
                instance['abstract_template_name'] = t


    with (topology_dir / f'{subckt}.verilog.json').open( 'wt') as fp:
        json.dump( verilog_json_d, fp=fp, indent=2)


def extract_netlist_files(netlist_dir,netlist_file):
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

    assert len(netlist_files) == 1, "Only one .sp file allowed"

    return netlist_files[0]


def start_viewer(working_dir, pnr_dir, variant):

    viewer_dir = pathlib.Path(__file__).resolve().parent.parent / 'Viewer'
    if not viewer_dir.exists():
        logger.warning(f'Viewer could not be located.')
        return

    local_viewer_dir = working_dir/'Viewer'
    if not local_viewer_dir.exists():
        os.mkdir(local_viewer_dir)
        os.mkdir(local_viewer_dir/'INPUT')
        os.symlink(viewer_dir/'index.html', local_viewer_dir/'index.html')
        os.symlink(viewer_dir/'js', local_viewer_dir/'js', target_is_directory=True)

    shutil.copy(pnr_dir/f'{variant}.json', local_viewer_dir/'INPUT'/f'{variant}.json')

    stderr = sys.stderr
    Handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(working_dir/'Viewer'))
    with socketserver.TCPServer(('localhost', 0), Handler) as httpd:
        logger.info(f'Please view layout at http://localhost:{httpd.server_address[1]}/?design={variant}')
        logger.info(f'Please type Ctrl + C to continue')
        with open(os.devnull, 'w') as fp:
            sys.stdout = sys.stderr = fp
            try:
                httpd.serve_forever()
            except KeyboardInterrupt:
                pass
    sys.stderr = stderr
    logger.info(f'Viewer terminated')


def schematic2layout(netlist_dir, pdk_dir, netlist_file=None, subckt=None, working_dir=None, flatten=False, nvariants=1, effort=0, extract=False, log_level=None, verbosity=None, generate=False, regression=False, uniform_height=False, PDN_mode=False, 
                    flow_start=None, flow_stop=None, router_mode='top_down', gui=False, skipGDS=False, lambda_coeff=1.0, reference_placement_verilog_json=None, nroutings=1, viewer=False):

    steps_to_run = build_steps( flow_start, flow_stop)

    logmanager.reconfigure_loglevels(file_level=log_level, console_level=verbosity)

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

    if regression:
        # Copy regression results in one dir
        regression_dir = working_dir / 'regression'
        regression_dir.mkdir(exist_ok=True)

    results = []

    # Generate hierarchy
    topology_dir = working_dir / '1_topology'
    if '1_topology' in steps_to_run:
        netlist = extract_netlist_files(netlist_dir,netlist_file)
        if subckt is None:
            subckt = netlist.stem

        logger.info(f"READ file: {netlist} subckt={subckt}, flat={flatten}")

        topology_dir.mkdir(exist_ok=True)
        primitives = generate_hierarchy(netlist, subckt, topology_dir, flatten, pdk_dir, uniform_height)

        gen_more_primitives( primitives, topology_dir, subckt)

        with (topology_dir / '__primitives__.json').open( 'wt') as fp:
            json.dump( primitives, fp=fp, indent=2)
    else:
        if subckt is None:
            subckt = extract_netlist_files(netlist_dir,netlist_file).stem

        with (topology_dir / '__primitives__.json').open( 'rt') as fp:
            primitives = json.load(fp)

    # Generate primitives
    primitive_dir = (working_dir / '2_primitives')
    primitive_dir_wo_tap = (working_dir / '2_primitives/wo_tap')
    if '2_primitives' in steps_to_run:
        primitive_dir.mkdir(exist_ok=True)
        primitive_dir_wo_tap.mkdir(exist_ok=True)
        for block_name, block_args in primitives.items():
            logger.debug(f"Generating primitive: {block_name}")
            uc = generate_primitive(block_name, **block_args, pdkdir=pdk_dir, outputdir=primitive_dir, netlistdir=netlist_dir)
            generate_primitive(block_name, **block_args, pdkdir=pdk_dir, outputdir=primitive_dir_wo_tap, netlistdir=netlist_dir, bodyswitch = 0)
            if hasattr(uc, 'metadata'):
                primitives[block_name]['metadata'] = copy.deepcopy(uc.metadata)
        
        with (primitive_dir / '__primitives__.json').open( 'wt') as fp:
            json.dump( primitives, fp=fp, indent=2)
    else:
        with (primitive_dir / '__primitives__.json').open( 'rt') as fp:
            primitives = json.load(fp)

    # run PNR tool
    pnr_dir = working_dir / '3_pnr'

    sub_steps = [step for step in steps_to_run if '3_pnr:' in step]
    if sub_steps:
        pnr_dir.mkdir(exist_ok=True)
        variants = generate_pnr(topology_dir, primitive_dir, pdk_dir, pnr_dir, subckt, primitives=primitives, nvariants=nvariants, effort=effort, extract=extract, gds_json=not skipGDS, PDN_mode=PDN_mode, router_mode=router_mode, gui=gui, skipGDS=skipGDS, steps_to_run=sub_steps, lambda_coeff=lambda_coeff, reference_placement_verilog_json=reference_placement_verilog_json, nroutings=nroutings)
        results.append( (subckt, variants))

        assert gui or router_mode == 'no_op' or '3_pnr:check' not in sub_steps or len(variants) > 0, f"No layouts were generated for {subckt}. Cannot proceed further. See LOG/align.log for last error."

        # Generate necessary output collateral into current directory
        for variant, filemap in variants.items():
            if filemap['errors'] > 0:
                (working_dir / filemap['errfile'].name).write_text(filemap['errfile'].read_text())

            if viewer:
                start_viewer(working_dir, pnr_dir, variant)
            elif os.getenv('ALIGN_HOME', False):
                shutil.copy(pnr_dir/f'{variant}.json',
                            pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/f'{variant}.json')


            assert skipGDS or 'gdsjson' in filemap
            if 'gdsjson' in filemap:
                convert_GDSjson_GDS(filemap['gdsjson'], working_dir / f'{variant}.gds')
                print("Use KLayout to visualize the generated GDS:",working_dir / f'{variant}.gds')

            assert skipGDS or 'python_gds_json' in filemap
            if 'python_gds_json' in filemap:
                convert_GDSjson_GDS(filemap['python_gds_json'], working_dir / f'{variant}.python.gds')
                print("Use KLayout to visualize the python generated GDS:",working_dir / f'{variant}.python.gds')

            assert skipGDS or 'lef' in filemap
            if 'lef' in filemap:
                (working_dir / filemap['lef'].name).write_text(filemap['lef'].read_text())

            if extract:
                (working_dir / filemap['cir'].name).write_text(filemap['cir'].read_text())

            # Generate PNG
            if generate:
                generate_png(working_dir, variant)

            # Copy regression results in one dir
            # SMB: Do we use this; let's get rid of it
            if regression:
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

