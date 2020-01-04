import argparse
from .main import schematic2layout

class CmdlineParser():

    def __init__(self, *args, **kwargs):
        parser = argparse.ArgumentParser(*args, **kwargs,
            description="directory path for input circuits")
        parser.add_argument("netlist_dir",
                            type=str,
                            help='Path to netlist directory')
        parser.add_argument("-p",
                            "--pdk_dir",
                            type=str,
                            required=True,
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
                            help='Top subckt defination in file.\
                            \nIf no name given it takes file name as subckt name. \
                            \nIf there are instances at top level,\
                            a new subckt is created of name filename')
        parser.add_argument(
                            "-flat",
                            "--flatten",
                            type=int,
                            default=0,
                            help='1 = flatten the netlist, 0= read as hierahical netlist')
        parser.add_argument("-U_mos",
                            "--unit_size_mos",
                            type=int,
                            default=10,
                            help='no of fins in unit size')
        parser.add_argument("-U_cap",
                            "--unit_size_cap",
                            type=int,
                            default=10,
                            help='no of fins in unit size')
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
        parser.add_argument("-c",
                            "--check",
                            action='store_true',
                            help='Set to true to run LVS / DRC checks (Default False)')
        parser.add_argument("-x",
                            "--extract",
                            action='store_true',
                            help='Set to true to extract post-layout netlist')
        self.parser = parser

    def parse_args(self, *args, **kwargs):
        arguments = self.parser.parse_args(*args, **kwargs)
        schematic2layout(**vars(arguments))
