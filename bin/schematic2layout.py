#!/usr/bin/env python
import argparse
import align

if __name__ == '__main__':
# %%
    PARSER = argparse.ArgumentParser(
        description="directory path for input circuits")
    PARSER.add_argument("netlist_dir",
                        type=str,
                        help='Path to netlist directory')
    PARSER.add_argument("-p",
                        "--pdk_dir",
                        type=str,
                        required=True,
                        help='Path to PDK directory')
    PARSER.add_argument("-w",
                        "--working_dir",
                        type=str,
                        default=None,
                        help='Path to working directory')
    PARSER.add_argument("-f",
                        "--file",
                        type=str,
                        default=None,
                        help='Name of file in netlist directory. \
                            \nIf no filename is given, it reads all files in netlist directory')
    PARSER.add_argument("-s",
                        "--subckt",
                        type=str,
                        default=None,
                        help='Top subckt defination in file.\
                        \nIf no name given it takes file name as subckt name. \
                        \nIf there are instances at top level,\
                        a new subckt is created of name filename')
    PARSER.add_argument(
                        "-flat",
                        "--flat",
                        type=int,
                        default=0,
                        help='1 = flatten the netlist, 0= read as hierahical netlist')
    PARSER.add_argument("-U_mos",
                        "--unit_size_mos",
                        type=int,
                        default=10,
                        help='no of fins in unit size')
    PARSER.add_argument("-U_cap",
                        "--unit_size_cap",
                        type=int,
                        default=10,
                        help='no of fins in unit size')
    args = PARSER.parse_args()
# %%
    align.schematic2layout(args.netlist_dir, args.pdk_dir, args.file, args.subckt, args.working_dir, args.flat, args.unit_size_mos, args.unit_size_cap)
