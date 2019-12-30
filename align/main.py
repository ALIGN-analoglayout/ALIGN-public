import pathlib
import subprocess

from .compiler import generate_hierarchy
from .cell_fabric import generate_primitive
from .compiler.util import logging

def schematic2layout(netlist_dir, pdk_dir, netlist_file=None, subckt_name=None, working_dir=None, flatten_heirarchy=False, unit_size_mos=10, unit_size_cap=10):

    if working_dir is None:
        working_dir = pathlib.Path.cwd().resolve()

    netlist_dir = pathlib.Path(netlist_dir).resolve()
    if not netlist_dir.is_dir():
        logging.error("Netlist directory doesn't exist. Please enter a valid directory path")
        print("Netlist directory doesn't exist. Please enter a valid directory path")
        exit(0)

    netlist_files = [x for x in netlist_dir.iterdir() if x.is_file() and x.suffix in ('.sp', '.cdl')]
    if not netlist_files:
        print("No spice files found in netlist directory. Exiting...")
        logging.error(
            "No spice files found in netlist directory. Exiting...")
        exit(0)

    if netlist_file:
        netlist_files = [x for x in netlist_files if netlist_file == x.name]
        if not netlist_files:
            print(f"No spice file {netlist_file} found in netlist directory. Exiting...")
            logging.error(
                f"No spice files {netlist_file} found in netlist directory. Exiting...")
            exit(0)

    for netlist in netlist_files:
        if subckt_name is None:
            subckt = netlist.stem
        else:
            subckt = subckt_name
        logging.info(f"READ file: {netlist} subckt_name={subckt}, flat={flatten_heirarchy}")
        primitives = generate_hierarchy(netlist, subckt, working_dir / '1_SCI', flatten_heirarchy, unit_size_mos , unit_size_cap)
        for block_name, block_args in primitives.items():
            generate_primitive(block_name, **block_args, pinswitch=0, pdkdir=pdk_dir, outputdir=working_dir / '2_primitives')
        # lef_generator = working_dir / '1_SCI' / f'{subckt}_lef.sh'
        # lef_generator.chmod(0o755)
        # subprocess.run(['/bin/bash', '-c', str(lef_generator), 'python3'])