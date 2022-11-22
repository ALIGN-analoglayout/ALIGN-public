import argparse
from .main import schematic2layout
from . import __version__
import os
from .utils import logmanager

import logging
logger = logging.getLogger(__name__)


class CmdlineParser():

    def __init__(self, *args, **kwargs):
        align_home = os.environ.get( 'ALIGN_HOME', None)

        parser = argparse.ArgumentParser(*args, **kwargs,
            description="directory path for input circuits")
        parser.add_argument("netlist_dir",
                            type=str,
                            help='Path to netlist directory')
        parser.add_argument("-p",
                            "--pdk_dir",
                            type=str,
                            required=align_home is None,
                            default=None if align_home is None else align_home + '/pdks/FinFET14nm_Mock_PDK',
                            help='Path to PDK directory')
        parser.add_argument("-w",
                            "--working_dir",
                            type=str,
                            default=None,
                            help='Path to working directory')
        parser.add_argument("-f",
                            "--netlist_file",
                            type=str,
                            default=None,
                            help='Name of file in netlist directory. \
                                \nIf no filename is given, it reads all files in netlist directory')
        parser.add_argument("-s",
                            "--subckt",
                            type=str,
                            default=None,
                            help='Top subckt definition in file.\
                            \nIf no name given it takes file name as subckt name. \
                            \nIf there are instances at top level,\
                            a new subckt is created of name filename')
        parser.add_argument(
                            "-flat",
                            "--flatten",
                            type=int,
                            default=0,
                            help='1 = flatten the netlist, 0= read as hierahical netlist')
        parser.add_argument("-n",
                            "--nvariants",
                            type=int,
                            default=1,
                            help='Number of layout candidates to (attempt to) generate')
        parser.add_argument("-e",
                            "--effort",
                            type=int,
                            default=0,
                            help='Amount of effort to dedicate to alternate layouts')
        parser.add_argument("-x",
                            "--extract",
                            action='store_true',
                            help='Set to true to extract post-layout netlist')
        # parser.add_argument( "-g", "--generate",
        #                     action='store_true',
        #                     help="Set the true to generate png")
        log_level, verbosity = logmanager.get_loglevels()
        parser.add_argument( "-l", "--log",
                            dest="log_level",
                            choices=['DEBUG','INFO','WARNING','ERROR','CRITICAL'],
                            default=log_level,
                            help="Logfile logging level (default: %(default)s)")
        parser.add_argument( "-v", "--verbosity",
                            dest="verbosity",
                            choices=['DEBUG','INFO','WARNING','ERROR','CRITICAL'],
                            default=verbosity,
                            help="Console logging level (default: %(default)s)")
        parser.add_argument("-r",
                            "--regression",
                            action='store_true',
                            help='Set to true to copy <dsign>.gds.json to top level (Default False)')
        parser.add_argument("-u",
                            "--uniform_height",
                            action='store_true',
                            help='Set to true to use cells of uniform height (Default False)')
        parser.add_argument("-pdn",
                            "--PDN_mode",
                            action='store_true',
                            help='Set to true to run power delivery network code (Default False)')
        parser.add_argument('--version',
                            action='version',
                            version='%(prog)s ' + __version__)

        parser.add_argument('--flow_start',
                            type=str,
                            help='Stage to start the flow. Previous stages are skipped.')
        parser.add_argument('--flow_stop',
                            type=str,
                            help='Stage after which to stop the flow. Subsequent stages are skipped.')

        parser.add_argument('--router_mode',
                            type=str,
                            default='top_down',
                            choices=['top_down','bottom_up','no_op'],
                            help='Router mode')

        parser.add_argument('--router',
                            type=str,
                            default='astar',
                            choices=['astar','hanan'],
                            help='Router to use')

        parser.add_argument('--gui',
                            action='store_true',
                            help='Run in GUI mode')

        parser.add_argument('--skipGDS',
                            action='store_true',
                            help='Don\'t generate GDS files.')

        parser.add_argument('--lambda_coeff',
                            type=float,
                            default=1.0,
                            help='Multiplier for hpwl in placer cost function.')

        parser.add_argument('--nroutings',
                            type=int,
                            default=1,
                            help='Maximum number of routings to generate.')

        parser.add_argument('--viewer',
                            action='store_true',
                            help='Start lightweight viewer.')

        parser.add_argument('--select_in_ILP',
                            action='store_true',
                            help='Use ILP to determine subcircuit selection.')

        parser.add_argument('--place_using_ILP',
                            action='store_true',
                            help='Use ILP to determine subcircuit selection.')

        parser.add_argument('--use_analytical_placer',
                            action='store_true',
                            help='Use analytical placer.')

        parser.add_argument('--placer_sa_iterations',
                            type=int,
                            default=10000,
                            help="Iterations used by the placer's SA algorithm.")

        parser.add_argument('--seed',
                            type=int,
                            default=0,
                            help='Random number generator seed for the placement algorithm')

        parser.add_argument('--ilp_solver',
                            type=str,
                            default='symphony',
                            choices=['symphony', 'lpsolve'],
                            help='ILP Solver used by placer ')


        parser.add_argument('--placer_ilp_runtime',
                            type=int,
                            default=1,
                            help="Runtime limit in seconds for ILP in each iteration of placement")
        self.parser = parser

    def parse_args(self, *args, **kwargs):
        if args:
            logger.debug(f"Command line arguments: {' '.join(args[0])}")
        arguments = self.parser.parse_args(*args, **kwargs)
        try:
            return schematic2layout(**vars(arguments))
        except Exception:
            logger.exception("Fatal Error. Cannot proceed")
            return None
