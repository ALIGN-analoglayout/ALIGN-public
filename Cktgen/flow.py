#!/usr/bin/env python

import argparse
import subprocess
import os

def cmdline():
    parser = argparse.ArgumentParser( description="Run ADR flow")
    parser.add_argument( "-s", "--script", type=str, default="cktgen.py")
    parser.add_argument( "-p", "--port", type=str, default="8082")
    parser.add_argument( "-td", "--techdir", type=str, default="../DetailedRouter/DR_COLLATERAL_Generator/strawman1")
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

    args = parser.parse_args()

    def b( value, tag): return f" {tag}" if value else ""
    def c( value, tag): return f" {tag} {value}" if value != "" else ""

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

    print( f"SCRIPT  = {args.script}")
    print( f"PORT    = {args.port}")
    print( f"TECHDIR = {args.techdir}")
    print( f"TECHFILE = {args.techfile}")
    print( f"INPUTVOL = {args.inputvol}")
    print( f"OUTPUTVOL = {args.outputvol}")
    print( f"ROUTERVOL = {args.routervol}")
    print( f"SKIPROUTER = {args.skiprouter}")
    print( f"SKIPGENERATE = {args.skipgenerate}")
    print( f"STARTVIEWER = {args.startviewer}")
    print( f"PLACERJSON = {args.placer_json}")
    print( f"GRJSON = {args.gr_json}")
    print( f"SOURCE = {args.source}")
    print( f"SMALL = {args.small}")
    print( f"NETS_TO_ROUTE = {args.nets_to_route}")
    print( f"NETS_NOT_TO_ROUTE = {args.nets_not_to_route}")

    M_INPUT = f"--mount source={args.inputvol},target=/Cktgen/INPUT"
    M_INPUT_VIEWER = f"--mount source={args.inputvol},target=/public/INPUT"
    M_out = f"--mount source={args.outputvol},target=/Cktgen/out"
    M_DR_COLLATERAL = f"--mount source={args.routervol},target=/Cktgen/DR_COLLATERAL"

    def run_sh( cmd, tag=None):
        ret = subprocess.run( [cmd],  shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', check=True)
        print(ret)
        print(ret.stdout)
        if ret.returncode != 0:
            if tag is not None:
                print( f"ERROR: Failed to {tag}")
            exit(ret.returncode)


    ret = run_sh( f'docker volume rm -f {args.routervol}', f'remove volume {args.routervol}')

    ret = run_sh( f'(cd {args.techdir} && tar cvf - .) | docker run --rm {M_DR_COLLATERAL} -i ubuntu bash -c "cd /Cktgen/DR_COLLATERAL && tar xvf -"', 'create DR_COLLATERAL')

    if not args.skipgenerate:
        ret = run_sh( f'docker volume rm -f {args.outputvol}',
                      f'remove volume {args.outputvol}')

        ret = run_sh( f'docker run --rm {M_INPUT} {M_DR_COLLATERAL} cktgen bash -c "source /general/bin/activate && cd /Cktgen && python {args.script} -n mydesign {route}{showglobalroutes}{showmetaltemplates}{source}{placer_json}{gr_json}{small}{nets_to_route}{nets_not_to_route}"', 'run Cktgen')

    if not args.skiprouter:
        #ROUTER_IMAGE="darpaalign/detailed_router"
        #ROUTER_IMAGE="stevenmburns/intel_detailed_router"
        ROUTER_IMAGE="nikolai_router"
        ret = run_sh( f'docker run --rm {M_out} {M_INPUT} {M_DR_COLLATERAL} {ROUTER_IMAGE} bash -c "cd /Cktgen && amsr.exe -file INPUT/ctrl.txt"', 'run detailed_router')
        ret = run_sh( f'docker run --rm {M_out} {M_INPUT} {M_DR_COLLATERAL} cktgen bash -c "source /general/bin/activate; cd /Cktgen && python {args.script} --consume_results -n mydesign {source}{placer_json}{small}{no_interface}"', 'run Cktgen (consume)')

    if "STARTVIEWER" in os.environ and os.envion["STARTVIEWER"] == "YES":
        ret = run_sh( f'docker run --rm {M_INPUT_VIEWER} -p{args.port}:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate && cd /public && python -m http.server"', 'run viewer_image')

if __name__ == "__main__":
    cmdline()
