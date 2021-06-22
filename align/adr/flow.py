#!/usr/bin/env python

import argparse
import subprocess
import os
import sys
import logging

from align.adr import cktgen, cktgen_physical_from_json

import logging
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

logger.addHandler(logging.StreamHandler(sys.stdout))

def run_sh( cmd, tag=None):
    tagstr = '' if tag is None else f' {tag}'
    logger.info( f'Calling{tagstr} {cmd}')
    # bufsize=1 means line buffered
    with subprocess.Popen( [cmd], shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', universal_newlines=True, bufsize=1) as p:
        for line in p.stdout:
            line = line.rstrip( '\n')
            logger.info(line)
        p.wait()
        if p.returncode != 0:
            logger.info( f'Failed {p.returncode}{tagstr} {cmd}')
            exit(p.returncode)
        else:
            logger.info( f'Finished{tagstr} {cmd}')

def run_router_in_container( args):
    M_INPUT = f"--mount source={args.inputvol},target=/Cktgen/INPUT"
    M_out = f"--mount source={args.outputvol},target=/Cktgen/out"
    M_DR_COLLATERAL = f"--mount source={args.routervol},target=/Cktgen/DR_COLLATERAL"

    run_sh( f'docker volume rm -f {args.outputvol}', f'remove volume {args.outputvol}')
    run_sh( f'rm -fr out', "Remove old out directory")        

    run_sh( f'docker volume rm -f {args.inputvol}', f'remove volume {args.inputvol}')
    run_sh( f'(cd INPUT && tar cvf - .) | docker run --rm {M_INPUT} -i ubuntu bash -c "cd /Cktgen/INPUT && tar xvf -"', 'create INPUT')

    run_sh( f'docker volume rm -f {args.routervol}', f'remove volume {args.routervol}')
    run_sh( f'(cd {args.techdir} && tar cvf - .) | docker run --rm {M_DR_COLLATERAL} -i ubuntu bash -c "cd /Cktgen/DR_COLLATERAL && tar xvf -"', 'create DR_COLLATERAL')

    run_sh( f'docker volume rm -f {args.outputvol}', f'remove volume {args.outputvol}')

    #ROUTER_IMAGE="darpaalign/detailed_router"
    #ROUTER_IMAGE="stevenmburns/intel_detailed_router"
    ROUTER_IMAGE="nikolai_router"

    run_sh( f'docker run --name sam {M_out} {M_INPUT} {M_DR_COLLATERAL} {ROUTER_IMAGE} bash -c "cd /Cktgen && amsr.exe -file INPUT/ctrl.txt"', 'run detailed_router')

    run_sh( f'docker cp sam:/Cktgen/out .', 'copy output directory')  
    run_sh( f'docker rm sam', 'remove detailed_router container')

def run_router_executable( args):
    run_sh( f'{args.router_executable} -file INPUT/ctrl.txt', 'run detailed_router')


def cmdline( argv):
    parser = argparse.ArgumentParser( description="Run ADR flow")

    parser.add_argument( "--viewer_input_dir", type=str, default="")
    parser.add_argument( "--router_executable", type=str, default="")

    parser.add_argument( "-td", "--techdir", type=str, default="../DetailedRouter/DR_COLLATERAL_Generator/strawman1")
    parser.add_argument( "-tm", "--topmetal", type=str, default="")
    parser.add_argument( "-tf", "--techfile", type=str, default="Process.json")
    parser.add_argument( "-iv", "--inputvol", type=str, default="inputVol")
    parser.add_argument( "-ov", "--outputvol", type=str, default="outputVol")
    parser.add_argument( "-rv", "--routervol", type=str, default="routerStrawman")
    parser.add_argument( "-sr", "--skiprouter", action='store_true')
    parser.add_argument( "-sg", "--skipgenerate", action='store_true')
    parser.add_argument( "-sv", "--startviewer", action='store_true')
    parser.add_argument( "-sgr", "--showglobalroutes", action='store_true')
    parser.add_argument( "-smt", "--showmetaltemplates", action='store_true')
    parser.add_argument( "-sar", "--skipactualrouting", action='store_true')
 
    parser.add_argument( "-pj", "--placer_json", type=str, default="")
    parser.add_argument( "-gj", "--gr_json", type=str, default="")
    parser.add_argument( "-src", "--source", type=str, default="")
    parser.add_argument( "--small", action='store_true')
    parser.add_argument( "--no_interface", action='store_true')
    parser.add_argument( "--nets_to_route", type=str, default="")
    parser.add_argument( "--nets_not_to_route", type=str, default="")

    args = parser.parse_args( argv)

    assert not args.skipgenerate

    if args.viewer_input_dir == "" and "ALIGN_HOME" in os.environ:
        args.viewer_input_dir = os.environ["ALIGN_HOME"] + "/Viewer/INPUT"

    def b( value, tag): return f" {tag}" if value else ""
    def c( value, tag): return f" {tag} {value}" if value else ""

    topmetal = c( args.topmetal, "--topmetal")

    route = b( not args.skipactualrouting, "--route")
    placer_json = c( args.placer_json, "--placer_json")
    gr_json = c( args.gr_json, "--gr_json")
    source = c( args.source, "--source")
    small = b( args.small, "--small")
    no_interface = b( args.no_interface, "--no_interface")

    showglobalroutes = b( args.showglobalroutes, "--show_global_routes")
    showmetaltemplates = b( args.showmetaltemplates, "--show_metal_templates")

    nets_to_route = c( args.nets_to_route, "--nets_to_route")
    nets_not_to_route = c( args.nets_not_to_route, "--nets_not_to_route")

    run_sh( f'rm -rf DR_COLLATERAL', "Remove old DR_COLLATERAL directory")
    run_sh( f'cp -pr {args.techdir} DR_COLLATERAL')

    run_sh( f'mkdir -p INPUT')

    cmd = f'-n mydesign {route}{showglobalroutes}{showmetaltemplates}{source}{placer_json}{gr_json}{small}{nets_to_route}{nets_not_to_route}{topmetal}{no_interface}'
    cmdlist = list(filter( lambda x: x != '', cmd.split( ' ')))
    cktgen_args, tech = cktgen.parse_args( cmdlist)
    cktgen_physical_from_json.main( cktgen_args, tech)

    if not args.skiprouter:
        if args.router_executable:
            run_router_executable( args)
        else:
            run_router_in_container( args)
        cktgen.consume_results( cktgen_args, tech)
        run_sh( f'cp INPUT/mydesign_dr_globalrouting.json {args.source + ".json"}')

    if args.viewer_input_dir and args.source:
        run_sh( f'cp INPUT/mydesign_dr_globalrouting.json {args.viewer_input_dir + "/" + args.source + ".json"}')

if __name__ == "__main__":
    cmdline( sys.argv[1:])
