#! /scratch/anaconda/bin/python3
'''This file runs ChargeFlow'''
import logging
import argparse
import time
import os
import warnings
import pandas as pd
import pprint as pp
from functools import wraps, singledispatch

from classdesc import subcircuit, net, connection, branch
from afunctions import get_dirs, \
                       get_net_under_test, \
                       extract_spice, \
                       extract_verilog_json, \
                       map_pins_stov, \
                       get_subckt_under_test, \
                       prepare_print_statement, \
                       generate_tran_data, \
                       store_pin_currents_in_csv, \
                       measure_branch_current_spice, \
                       measure_branch_current_verilog, \
                       clean, \
                       prepare_cf_const, \
                       write_const_file
					  


parser = argparse.ArgumentParser(description = 'This functions generates ML \
                                 models from performance constraints.')
parser.add_argument('-design', '--design', type = str, metavar = '',
                    required = True, help = 'Netlist under test')


args = parser.parse_args()
logging.basicConfig(filename = 'run.log', filemode = 'w', level = logging.INFO,
                    format = '%(name)s - %(levelname)s - %(message)s')

WORK_DIR = os.getcwd()


def main():
    '''
    Run the entire script
    '''
    design = args.design.upper()
    fdict = get_dirs(WORK_DIR, design)
    clean(fdict, design)
    nutest = get_net_under_test(fdict)
    ssubcktlist = extract_spice(fdict, nutest)
    vsubcktlist = extract_verilog_json(fdict, nutest, design)
    ssutest = get_subckt_under_test(fdict, design, ssubcktlist)
    vsutest = get_subckt_under_test(fdict, design, vsubcktlist)
    pinmap = map_pins_stov(fdict, design, nutest, ssutest, vsutest)
    prepare_print_statement(fdict, design, ssutest)
    generate_tran_data(fdict, design)
    store_pin_currents_in_csv(fdict, design)
    measure_branch_current_spice(fdict, design, ssutest)
    measure_branch_current_verilog(fdict, design, ssutest, vsutest, pinmap)
    cf_const = prepare_cf_const(fdict, design)
    write_const_file(fdict, design, cf_const)
    # # print(subcktdict[design])


if __name__ == "__main__":
    main()
