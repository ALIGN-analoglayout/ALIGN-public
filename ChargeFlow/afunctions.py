import logging
import time
import os
import csv
import warnings
import pickle
import numpy as np
import json
import re
import itertools
import pandas as pd
from functools import wraps

from classdesc import subcircuit, net, connection, branch

def logger(func):
    '''
    Log function name before running
    '''
    @wraps(func)
    def wrapper(*args, **kwargs):
        logging.info('Function name: %s' % func.__name__)
        return func(*args, **kwargs)
    return wrapper

def timer(func):
    '''
    Store runtime in log file
    '''
    @wraps(func)
    def wrapper(*args, **kwargs):
        tstart = time.time()
        result = func(*args, **kwargs)
        tend = time.time()
        logging.info('Runtime: %f',(tend-tstart))
        return result
    return wrapper

@logger
@timer
def get_net_under_test(fdict):
    '''
    User can specify nets of a circuit to set charge flow constraints
    '''
    try:
        fnets = open(fdict["fnets"], 'r')
    except FileNotFoundError as err:
        logging.info('All nets will be used only for the ML model.')
        return []
    else:
        nutest = ' '.join(fnets.readlines()).split()  # joins multiple lines if given
        nutest = [net.upper() for net in nutest]
        logging.info(f'{nutest} will be used only for the ML model.')
        return nutest

@logger
@timer
def get_dirs(WORK_DIR, design):
    '''
    Generate necessary filenames from the design name and return a dictionary
    containing the file directories
    '''
    files = ["fspice", "fspicetb", "fvjson", "fnets", "fprint"]
    exts = [".sp", "_tb.sp", ".verilog.json", "_nets.txt", "_print.inc"]
    fdict = dict()

    for file, ext in zip(files, exts):
        fdict[file] = WORK_DIR +  "/" + design + "/" + design + ext
    fdict["main"] = WORK_DIR +  "/" + design
    return fdict

def net_is_under_test(net, nets_under_test):
    '''Check if a net is under test'''
    if net in nets_under_test:
        return True
    else:
        return False

def find_pin_in_netlist(tnode, netlist):
    for node in netlist:
        if node.name == tnode:
            return node 
    return None 

def store_connectivity_spice(line, netlist, nutest):
    '''For each device, store its connectivity to appropriate nets'''
    # print(f"line: {line}")
    llist = line.strip().split()
    if line.strip().lower().startswith('m'):
        dname, plist = llist[0], llist[1:4]
    else:
        dname, plist = llist[0], llist[1:3]

    dname = dname.upper()   #Changed cases to keep coherence with verilog.json.
    plist = [item.upper() for item in plist]

    for i, tnodename in enumerate(plist): # ignoring body terminal for now
        # print(f"tnodename: {tnodename}")
        tconn = connection(dname, str(i+1))
        tnode = find_pin_in_netlist(tnodename, netlist)
        
        if tnode != None:
            tnode.connections.append(tconn)
            # print(f"Node exists.\ntnode: {tnode}")
        else:
            isundertest = True if tnodename in nutest else False
            tnode = net(tnodename, isundertest)
            tnode.connections.append(tconn)
            netlist.append(tnode)
            # print(f"Node does not exist.\ntnode: {tnode}")
            # print(tnode)
        # breakpoint()


@logger
@timer
def extract_spice(fdict, nutest):
    '''Store all necessary information from spice file'''
    subcktlist = list()
    try:
        fspice = open(fdict["fspice"], "r")
    except FileNotFoundError as err:
        logging.critical(err)
        exit()
    else:
        for line in fspice:
            if not line.strip().startswith("//"):
                line = line.lstrip('.')
                if line.lower().startswith("subckt"):
                    # print(line)
                    llist, netlist = line.strip().split(), list()
                    subckt_name, plist = llist[1].upper(), llist[2:]
                    for line in fspice:
                        if line.strip().lower().startswith("m") or \
                           line.strip().lower().startswith("r") or \
                           line.strip().lower().startswith("c"):
                           store_connectivity_spice(line, netlist, nutest)
                        elif line.strip().lstrip('.').lower().startswith("end"):
                            tsubckt = subcircuit(subckt_name, plist, netlist)
                            subcktlist.append(tsubckt)
                            logging.info("{}" .format(subcktlist[-1]))
                        else:
                            pass
        fspice.close()
    return subcktlist


@logger
def clean(fdict, design):
    local_dir = "/sims/"
    if os.path.exists(fdict["main"] + local_dir):
        os.chdir(fdict["main"] + local_dir)
        print(os.getcwd())
        os.system("rm -rf ./outputs_*")


def get_net_from_list(net, nlist):
    for item in nlist:
        # print(item.name)
        if item.name == net:
            return item
    return None

def get_pin_from_verilog(sconn, vconnlist):
    tkey = sconn.devicename
    for vconn in vconnlist:
        tlist = vconn.devicename.split('_')
        devlist = list()
        for item in tlist:
            if item.startswith('MP') or item.startswith('MN') or item.startswith('R'):
                devlist.append(item)
        # print(devlist)
        if tkey in devlist:
            # tvalue = '/'.join(mconn)
            tvalue = vconn.devicename + "/" + vconn.nodename
            return tkey, tvalue
    return tkey, None

@logger
@timer
def get_subckt_under_test(fdict, design, subcktlist):
    for subckt in subcktlist:
        if subckt.name == design:
            return subckt
    return None

@logger
@timer
def map_pins_stov(fdict, design, nutest, ssutest, vsutest):
    '''This function creates a dictionary to map pins from spice netlist to verilog netlist'''
    pinmap = dict()

    for tnode in nutest:
        tsnode = find_pin_in_netlist(tnode, ssutest.netlist)
        tvnode = find_pin_in_netlist(tnode, vsutest.netlist)

        if tvnode != None and tsnode != None:
            pinmap[tnode] = dict()
            for sconn in tsnode.connections:
                tkey, tvalue = get_pin_from_verilog(sconn, tvnode.connections)
                if tvalue == None:
                    print(tkey)
                    raise ValueError
                else:
                    if not tkey in pinmap[tnode]:
                        pinmap[tnode][tkey] = tvalue
        else:
            nutest.remove(tnode)
    return pinmap

def map_param_list_stov(fdict, dict_map_pins, param_name_list):
    pinlist = list()
    for item in param_name_list:
        ptype, net, device = item.split('_')
        pinlist.append(net + "\t" + dict_map_pins[net][device])
    pinlist = list(set(pinlist))
    with open(fdict["main"] + "/pins_mapped_to_verilog.txt", "w") as f:
        f.write('\n'.join(pinlist))

def get_pin_formal(netname, pinlist):
    for pin in pinlist:
        if pin["actual"] == netname:
            return pin["formal"]
    return None

@timer
@logger
def extract_verilog_json(fdict, nutest, design):
    '''Store all necessary information from verilog json file'''
    subcktlist = list()
    try:
        fvjson = open(fdict["fvjson"], "r")
    except FileNotFoundError as err:
        logging.critical(err)
        exit()
    else:    
        with open(fdict["fvjson"], "r") as fvjson:
            netlist_details = json.load(fvjson)
            for subckt in netlist_details["modules"]:
                if subckt["name"] == design:
                    t_instance_list = subckt["instances"]
                    netlist = list()
                    # tsubckt = subcircuit(subckt["name"], subckt["parameters"], netlist)
                    for instance in t_instance_list:
                        for pin in instance["fa_map"]:
                            if pin["actual"] in nutest:
                                tconn = connection(instance["instance_name"], pin["formal"])
                                tnode = find_pin_in_netlist(pin["actual"], netlist)
                                if tnode != None:
                                    tnode.connections.append(tconn)
                                else:
                                    tnode = net(pin["actual"], True) 
                                    tnode.connections.append(tconn)
                                    netlist.append(tnode)
                    tsubckt = subcircuit(subckt["name"], subckt["parameters"], netlist)
                    subcktlist.append(tsubckt)
        logging.info(subcktlist[-1])
        fvjson.close()
    return subcktlist

@timer
@logger
def prepare_print_statement(fdict, design, ssutest):
    logging.info("Preparing print file: {}" .format(fdict["fprint"]))

    print_statement = ".PRINT TRAN "
    for tnode in ssutest.netlist:
        if tnode.isundertest:
            for connection in tnode.connections:
                print_statement = print_statement + "I" + connection.nodename + "(I1." + connection.devicename + ") "
    logging.info("{}" .format(print_statement))

    with open(fdict["fprint"], 'w') as fprint:
        fprint.write(print_statement)

@timer
@logger
def generate_tran_data(fdict, design):
    tbfile_new = design + "_revised_tb.sp"
    os.chdir(fdict["main"])
    tb_details = ""
    with open(fdict["fspicetb"], 'r') as ftb_old:
        for line in ftb_old:
            tb_details = tb_details + line
    tb_details = tb_details + "\n" + "include \"./" + design + "_print.inc\"\n"

    logging.info("Doing transient simulations..." )
    with open(fdict["main"] + "/" + tbfile_new, 'w') as ftb_new:
        ftb_new.write(tb_details)
    os.system("spectre " + tbfile_new + " > " + design + ".log")

@timer
@logger
def store_pin_currents_in_csv(fdict, design):
    """
    This function just extracts pin current from the transient file generated
    by the spice transient simulation, does necessary string replacements,
     and saves the data in csv format.
    """
    logging.info("Generating branch currents from spice...")
    printfile = design + "_revised_tb.print"
    os.chdir(fdict["main"])

    if os.path.exists(fdict["main"] + "/pin_currents.txt"):
        os.system("rm -f pin_currents.txt")

    os.system("grep -vwE \"(\*|x|y)\" " + printfile + " > pin_currents.txt" )
    num_lines = sum(1 for line in open('pin_currents.txt'))

    # with open("pin_currents.txt", 'r') as fpin:
    blocks_in_transients = open("pin_currents.txt", 'r').read().count("time")
    # blocks_in_transients = temp.count("time")
    points_in_transients = int(num_lines/int(blocks_in_transients))
    logging.info("Blocks in PRINT file: {}" .format(blocks_in_transients))
    logging.info("Points in PRINT file: {}" .format(points_in_transients))

    """Create a dataframe consisting pin currents"""
    with open(fdict["main"]+ "/pin_currents.txt", 'r') as fpinc:
        lines = fpinc.readlines()
        rearranged_lines = ""
        for i in range(points_in_transients):
            # line = ""
            for j in range(blocks_in_transients):
                line_to_read = j*points_in_transients + i
                lines_string = lines[line_to_read].strip().replace(' m', 'e-3')
                lines_string = lines_string.replace(' u', 'e-6').replace(' n', 'e-9').replace(' p', 'e-12').replace(' f', 'e-15').replace(' a', 'e-18')
                templine = re.split(" +", lines_string.strip())
                if j == 0:
                    # rearranged_lines = rearranged_lines + ":".join(re.split("  +", lines[line_to_read].strip()))
                    rearranged_lines = rearranged_lines + ":".join(templine)
                else:
                    # print(lines[line_to_read].strip().split('\t'))
                    # rearranged_lines = rearranged_lines + ":" + ":".join(re.split("  +", lines[line_to_read].strip())[1:])
                    rearranged_lines = rearranged_lines + ":" + ":".join(templine[1:])
            rearranged_lines = rearranged_lines + "\n"
        # print(rearranged_lines)
    with open(fdict["main"] + "/pin_currents_new.csv", 'w') as fpinc:
        lines = fpinc.writelines(rearranged_lines)

def measure_branch_current_spice(fdict, design, ssutest):
    """
    This function estimates branch current from pin to pin for each time
    stamp of transient simulation. In the process, it considers each point in
    time stamp as isolated; identifies source/sinks for that point; measures
    branch current from source to sink for that point.

    """
    pin_currents = pd.read_csv(fdict["main"] + "/pin_currents_new.csv", delimiter= ':')
    branch_currents = pin_currents[['time']].copy()

    for tnode in ssutest.netlist:
        if tnode.isundertest:
            pins_tnode = ["i" + conn.nodename + "(I1." + conn.devicename + ")" \
                                  for conn in tnode.connections]
            logging.info(f"For net {tnode.name}, columns under test: {pins_tnode}\n")
            pin_pairs = itertools.combinations(pins_tnode, 2)
            pin_pairs = [list(item) for item in pin_pairs]
            tbranch_name = list()

            for ppair in pin_pairs:
                dev1 = ppair[0].rstrip(')').split('(')[1].lstrip('I1.')
                dev2 = ppair[1].rstrip(')').split('(')[1].lstrip('I1.')
                tbranch_name.append(tnode.name + "-" + dev1 + "-" + dev2)
                tnode.branches.append([dev1, dev2])

            tbranch_currents_row = dict.fromkeys(tbranch_name, 0)
            tbranch_currents = pd.DataFrame(columns = tbranch_name)

            logging.info("Branches:\n{}\n" .format(tbranch_name))

            with open(fdict["main"] + "/pin_currents_new.csv") as f:
                reader = csv.DictReader(f, delimiter = ':')
                for row in reader:
                    sources, sinks, total_i = list(), list(), 0
                    for pin in pins_tnode:
                        if float(row[pin]) > 0: 
                            # In transient data of spice, if a current goes in of  a pin, 
                            # it is shown with positive value. However, the pin is acting as a sink.
                            sinks.append(pin)
                        else: 
                            # In transient data of spice, if a current goes out of  a pin, 
                            # it is shown with negative value. However, the pin is acting as a source.
                            sources.append(pin)
                            total_i = total_i + -1*float(row[pin])


                    for source in sources:
                        for sink in sinks:  
                            dev1 = source.rstrip(')').split('(')[1].lstrip('I1.')
                            dev2 = sink.rstrip(')').split('(')[1].lstrip('I1.')                                                                         
                            prob_tbranch_name1 = tnode.name + "-" + dev1 + "-" + dev2
                            prob_tbranch_name2 = tnode.name + "-" + dev2 + "-" + dev1                            
                            tbranch_i = float(row[sink])*float(row[source])/total_i

                            if prob_tbranch_name1 in tbranch_currents_row:
                                tbranch_currents_row[prob_tbranch_name1] = tbranch_i
                            elif prob_tbranch_name2 in tbranch_currents_row:
                                tbranch_currents_row[prob_tbranch_name2] = -1*tbranch_i
                            else:
                                pass

                    tbranch_currents = tbranch_currents.append(tbranch_currents_row, ignore_index = True)

            branch_currents = pd.concat([branch_currents, tbranch_currents], axis = 1)

    branch_currents.to_csv(fdict["main"] + "/branch_currents_spice.csv", index = False, mode = 'w')



@timer
@logger
def measure_branch_current_verilog(fdict, design, ssutest, vsutest, pinmap):
    branch_currents_spice = pd.read_csv(fdict["main"] + "/branch_currents_spice.csv")
    branch_currents_verilog = branch_currents_spice[['time']].copy()

    for tnode in ssutest.netlist:
        if tnode.isundertest:
            for branch in tnode.branches:
                [ds1, ds2] = branch
                dv1, dv2 = pinmap[tnode.name][ds1], pinmap[tnode.name][ds2]

                # print(f"ds1: {ds1}, ds2: {ds2}")
                # print(f"dv1: {dv1}, dv2: {dv2}")                
                if dv1 != dv2:
                    pvbranch1 = tnode.name + "-" + dv1 + "-" + dv2
                    pvbranch2 = tnode.name + "-" + dv2 + "-" + dv1
                    sbranch = tnode.name + "-" + ds1 + "-" + ds2
                    # print(f"vbranch: {pvbranch1}, vbranchr: {pvbranch2}, sbranch: {sbranch}")
                    temp_df = branch_currents_spice[[sbranch]].copy()
                    # print(temp_df.head())
                    # temp_df = temp_df.rename(columns={sbranch: vbranch})
                    # print(temp_df.head())
                    if pvbranch1 in branch_currents_verilog.columns:
                        temp_df = temp_df.rename(columns={sbranch: pvbranch1})
                        # print(temp_df.head())
                        # print(all_branch_currents_verilog_df.head())
                        branch_currents_verilog[pvbranch1] = branch_currents_verilog[pvbranch1] + \
                                                                  temp_df[pvbranch1]
                        # print(all_branch_currents_verilog_df.head())
                    elif pvbranch2 in branch_currents_verilog.columns:
                        # print("2")                        
                        temp_df = temp_df.rename(columns={sbranch: pvbranch2})
                        branch_currents_verilog[pvbranch1] = branch_currents_verilog[pvbranch1] - \
                                                                  temp_df[pvbranch2]                        
                    else:
                        # print("3")                        
                        temp_df = temp_df.rename(columns={sbranch: pvbranch1})
                        branch_currents_verilog = pd.concat([branch_currents_verilog,\
                                                            temp_df],
                                                            axis = 1)  
    branch_currents_verilog.to_csv(fdict["main"] + "/branch_currents_verilog.csv", index = False, mode = 'w')  
 

@logger
@timer
def prepare_cf_const(fdict, design):

    cf_const_rms = dict()
    cf_const_max = dict()
    cf_const = list()

    branch_currents_verilog = pd.read_csv(fdict["main"] + "/branch_currents_verilog.csv")

    time = branch_currents_verilog["time"].to_numpy()
    delta_time = time[1:] - time[0:-1]

    for clmn in branch_currents_verilog.columns:
        if clmn.lower() != 'time':
            tcurrent = branch_currents_verilog[clmn].to_numpy()
            tcurrent_squared = np.square(tcurrent)
            tcurrent_squared_area = np.sum(0.5*(np.multiply(tcurrent_squared[1:] + 
                                    tcurrent_squared[0:-1], delta_time)))
            tcurrent_rms = np.sqrt(tcurrent_squared_area/(time[-1] - time[0]))
            tcurrent_max = np.max(tcurrent)
            cf_const_rms[clmn] = tcurrent_rms
            cf_const_max[clmn] = tcurrent_max

    cf_const_rms = {key: value/max(cf_const_rms.values()) for (key,value) in cf_const_rms.items()}
    cf_const_max = {key: value/max(cf_const_max.values()) for (key,value) in cf_const_max.items()}
    cf_const_rms = dict(sorted(cf_const_rms.items(), key = lambda item: item[1], reverse = True))

    for key in cf_const_rms: 
        tnode, tpin1, tpin2 = key.split('-')
        trms = round(cf_const_rms[key], 4)
        tmax = round(cf_const_max[key], 4)
        tcf_const = [tnode, tpin1, tpin2, str(trms), str(tmax)]
        cf_const.append(tcf_const)

    return cf_const

def write_const_file(fdict, design, cf_const):
    cf_const_file = fdict["main"] + "/" + design + ".cfconst"
    with open(cf_const_file, 'w') as fconst:
        for const in cf_const:
            fconst.write('\t'.join(const))
            fconst.write('\n')
    pass

    # for item in all_branch_currents_verilog_df.columns:
    # netname, prim1, prim2 = item.split('-')
    # squared_current = np.square(all_branch_currents_verilog_df[item].to_numpy())
    # time = all_branch_currents_spice_df["time"].to_numpy()
    # delta_time = time[1:] - time[0:-1]
    # area_of_the_transient = np.sum(0.5*(np.multiply(squared_current[1:] + squared_current[0:-1], delta_time)))
    # rms_current_from_int = np.sqrt(area_of_the_transient/(time[-1] - time[0]))
    # # rms_current = np.sqrt(np.mean(np.square(all_branch_currents_verilog_df[item].to_numpy())))
    # max_current =  np.max(all_branch_currents_verilog_df[item].to_numpy())
    # templist = [prim1, prim2, rms_current_from_int, max_current]
    # # print("RMS current regular: {}, RMS current from area: {}" .format(rms_current, rms_current_from_int))
    # # print("{} {} {}" .format(templist, netname, rms_current))
    # net.branchcurrents.append(templist)