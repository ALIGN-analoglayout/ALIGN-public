import pathlib
import shutil
import os
import json
import sys
import http.server
import socketserver
import functools

from .compiler import generate_hierarchy
from align.schema.library import read_lib_json
from .primitive import generate_primitives
from .pnr import generate_pnr
from .gdsconv.json2gds import convert_GDSjson_GDS
from .utils.gds2png import generate_png
from .utils import logmanager

import logging
logger = logging.getLogger(__name__)


def build_steps(flow_start, flow_stop):
    steps = ['1_topology', '2_primitives', '3_pnr']
    sub_steps = {'3_pnr': ['prep', 'place', 'gui', 'route']}

    unimplemented_start_points = set()
    unimplemented_stop_points = set()

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
        if (step,) == start_t:
            enabled = True
        if step in sub_steps:
            for sub_step in sub_steps[step]:
                if (step, sub_step) == start_t:
                    enabled = True
                if enabled:
                    steps_to_run.append(f'{step}:{sub_step}')
                if (step, sub_step) == stop_t:
                    assert enabled, f'Stopping flow before it started: {flow_start} {flow_stop}'
                    enabled = False
        else:
            if enabled:
                steps_to_run.append(f'{step}')
            if (step,) == stop_t:
                assert enabled, f'Stopping flow before it started: {flow_start} {flow_stop}'
                enabled = False

    logger.debug(f'Running flow steps {steps_to_run}')

    return steps_to_run


def extract_netlist_files(netlist_dir, netlist_file):
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
        logger.warning('Viewer could not be located.')
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
        logger.info('Please type Ctrl + C to stop viewer and continue')
        with open(os.devnull, 'w') as fp:
            sys.stdout = sys.stderr = fp
            try:
                httpd.serve_forever()
            except KeyboardInterrupt:
                pass
    sys.stderr = stderr


def schematic2layout(netlist_dir, pdk_dir, netlist_file=None, subckt=None, working_dir=None, flatten=False, nvariants=1, effort=0, extract=False,
                     log_level=None, verbosity=None, generate=False, regression=False, uniform_height=False, PDN_mode=False, flow_start=None,
                     flow_stop=None, router_mode='top_down', gui=False, skipGDS=False, lambda_coeff=1.0,
                     nroutings=1, viewer=False, select_in_ILP=False, place_using_ILP=False, place_using_PT=False, seed=0, use_analytical_placer=False, ilp_solver='symphony',
                     placer_sa_iterations=10000, placer_ilp_runtime=1, placer=None):

    steps_to_run = build_steps(flow_start, flow_stop)

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
        netlist = extract_netlist_files(netlist_dir, netlist_file)
        if subckt is None:
            subckt = netlist.stem.upper()
        else:
            subckt = subckt.upper()

        logger.info(f"Reading netlist: {netlist} subckt={subckt}, flat={flatten}")

        shutil.rmtree(topology_dir, ignore_errors=True)
        topology_dir.mkdir(exist_ok=True)
        primitive_lib = generate_hierarchy(netlist, subckt, topology_dir, flatten, pdk_dir)
    else:
        if subckt is None:
            subckt = extract_netlist_files(netlist_dir, netlist_file).stem
        primitive_lib = read_lib_json(topology_dir / '__primitives_library__.json')

    # Generate primitives
    primitive_dir = (working_dir / '2_primitives')

    sub_steps = [step for step in steps_to_run if '3_pnr:' in step]

    if '2_primitives' in steps_to_run:
        shutil.rmtree(primitive_dir, ignore_errors=True)
        primitive_dir.mkdir(exist_ok=True)
        primitives = generate_primitives(primitive_lib, pdk_dir, primitive_dir, netlist_dir)
        with (primitive_dir / '__primitives__.json').open('wt') as fp:
            json.dump(primitives, fp=fp, indent=2)
    elif sub_steps:
        with (primitive_dir / '__primitives__.json').open('rt') as fp:
            primitives = json.load(fp)

    # run PNR tool
    if sub_steps:
        pnr_dir = working_dir / '3_pnr'
        pnr_dir.mkdir(exist_ok=True)
        variants = generate_pnr(topology_dir, primitive_dir, pdk_dir, pnr_dir, subckt, primitives=primitives, nvariants=nvariants, effort=effort,
                                extract=extract, gds_json=not skipGDS, PDN_mode=PDN_mode, router_mode=router_mode, gui=gui, skipGDS=skipGDS,
                                steps_to_run=sub_steps, lambda_coeff=lambda_coeff,
                                nroutings=nroutings, select_in_ILP=select_in_ILP,
                                place_using_ILP=place_using_ILP, place_using_PT=place_using_PT, seed=seed,
                                use_analytical_placer=use_analytical_placer,
                                ilp_solver=ilp_solver,
                                placer_sa_iterations=placer_sa_iterations, placer_ilp_runtime=placer_ilp_runtime, placer=placer)

        results.append((subckt, variants))

        assert gui or router_mode == 'no_op' or '3_pnr:route' not in sub_steps or len(variants) > 0, \
            f"No layouts were generated for {subckt}. Cannot proceed further. See LOG/align.log for last error."

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
                print("Use KLayout to visualize the generated GDS:", working_dir / f'{variant}.gds')

            assert skipGDS or 'python_gds_json' in filemap
            if 'python_gds_json' in filemap:
                convert_GDSjson_GDS(filemap['python_gds_json'], working_dir / f'{variant}.python.gds')
                print("Use KLayout to visualize the python generated GDS:", working_dir / f'{variant}.python.gds')

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
