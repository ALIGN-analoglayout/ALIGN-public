import pathlib

from .compiler.compiler import compiler, compiler_output
from .compiler.util import logging

def schematic2layout(netlist_dir, netlist_file=None, subckt_name=None, working_dir=None, flatten_heirarchy=False, unit_size_mos=10, unit_size_cap=10):

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
        updated_ckt = compiler(netlist, subckt, flatten_heirarchy)
        compiler_output(netlist, updated_ckt, subckt, working_dir / 'Results', unit_size_mos , unit_size_cap)