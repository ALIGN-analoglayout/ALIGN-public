import pathlib

from .compiler import generate_hierarchy
from .cell_fabric import generate_primitive
from .compiler.util import logging

def schematic2layout(netlist_dir, pdk_dir, netlist_file=None, subckt_name=None, working_dir=None, flatten_heirarchy=False, unit_size_mos=10, unit_size_cap=10):

    if working_dir is None:
        working_dir = pathlib.Path.cwd().resolve()
    if not working_dir.is_dir():
        logging.error("Working directory doesn't exist. Please enter a valid directory path")
        print("Working directory doesn't exist. Please enter a valid directory path")
        exit(0)

    pdk_dir = pathlib.Path(pdk_dir).resolve()
    if not pdk_dir.is_dir():
        logging.error("PDK directory doesn't exist. Please enter a valid directory path")
        print("PDK directory doesn't exist. Please enter a valid directory path")
        exit(0)

    netlist_dir = pathlib.Path(netlist_dir).resolve()
    if not netlist_dir.is_dir():
        logging.error("Netlist directory doesn't exist. Please enter a valid directory path")
        print("Netlist directory doesn't exist. Please enter a valid directory path")
        exit(0)
    netlist_file = pathlib.Path(netlist_file).resolve()

    netlist_files = [x for x in netlist_dir.iterdir() if x.is_file() and x.suffix in ('.sp', '.cdl')]
    if not netlist_files:
        print("No spice files found in netlist directory. Exiting...")
        logging.error(
            "No spice files found in netlist directory. Exiting...")
        exit(0)

    if netlist_file:
        print(netlist_files)
        netlist_files = [x for x in netlist_files if netlist_file == x]
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
        # Generate hierarchy
        (working_dir / '1_topology').mkdir(exist_ok=True)
        primitives = generate_hierarchy(netlist, subckt, working_dir / '1_topology', flatten_heirarchy, unit_size_mos , unit_size_cap)
        # Generate primitives
        primitive_dir = (working_dir / '2_primitives')
        primitive_dir.mkdir(exist_ok=True)
        for block_name, block_args in primitives.items():
            generate_primitive(block_name, **block_args, pdkdir=pdk_dir, outputdir=working_dir / '2_primitives')
        # Generate .map & .lef inputs for PnR
        with (primitive_dir / (subckt + '.map')).open(mode='w') as mp, \
             (primitive_dir / (subckt + '.lef')).open(mode='w') as lp:
            for file_ in primitive_dir.iterdir():
                if file_.suffixes == ['.gds', '.json']:
                    true_stem = file_.stem.split('.')[0]
                    mp.write(f'{true_stem} {true_stem}.gds\n')
                elif file_.suffix == '.lef' and file_.stem != subckt:
                    lp.write(file_.read_text())
