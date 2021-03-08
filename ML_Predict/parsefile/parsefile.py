import os
import re
import logging
import pandas as pd

from utils.classdesc import param, simulation, specs, net, subcircuit
from utils.utils import get_lhs_samples

TRANSISTOR_PORTS = {0: "d", 1: "g", 2: "s", 3: "b"}
PASSIVE_PORTS = {0: "1", 1: "2"}

# nodes_under_test = list()
def pin_is_in_the_list(pin, netlist):
    for item in netlist:
        if item.name == pin:
            return item.id
    return None

def net_is_under_test(net, nets_under_test):
    if net in nets_under_test:
        return True
    else:
        return False

def extract_spice_netlist(WORK_DIR, design):
    spicefile = design + ".sp"
    tc_directory = "/" + design + "/"
    subcircuit_list = list()
    subcircuit_id = 0
    logging.info("Extracting spice file: {}" .format(spicefile))

    if not os.path.exists(WORK_DIR + tc_directory + spicefile):
        logging.critical("{} not found. Quitting MLPredict..." .format(spicefile))
        exit()

    with open(WORK_DIR + tc_directory + "nets_under_test.txt", "r") as fnode:
        for line in fnode:
            nets_under_test = line.strip().split()

    with open(WORK_DIR + tc_directory + spicefile, "r") as fspice:
        for line in fspice:
            if not line.strip().startswith("//"):
                if line.strip().startswith(".subckt"):
                    netlist = list()
                    netid = 0
                    list_from_line = line.strip().split()
                    subcircuit_name = list_from_line[1]
                    portlist = list_from_line[2:]
                    for line in fspice:
                        if line.strip().startswith("m") or line.strip().startswith("M"):
                            list_from_line = line.strip().split()
                            temp_list_with_drain_source = list_from_line[1:5]
                            device_name = list_from_line[0]
                            for i, pin in enumerate(temp_list_with_drain_source): # ignoring body terminal for now
                                get_netid = pin_is_in_the_list(pin, netlist)
                                if get_netid is not None:
                                    netlist[get_netid].connections.append([device_name, TRANSISTOR_PORTS[i]])
                                else:
                                    isundertest = net_is_under_test(pin, nets_under_test)
                                    netlist.append(net(pin, isundertest, netid))
                                    netlist[-1].connections.append([device_name, TRANSISTOR_PORTS[i]])
                                    netid = netid + 1
                        elif line.strip().startswith("r") or line.strip().startswith("c") or line.strip().startswith("l"):
                            list_from_line = line.strip().split()
                            device_name = list_from_line[0]
                            for i, pin in enumerate(list_from_line[1:3]):
                                get_netid = pin_is_in_the_list(pin, netlist)
                                if get_netid is not None:
                                    netlist[get_netid].connections.append([device_name, PASSIVE_PORTS[i]])
                                else:
                                    isundertest = net_is_under_test(pin, nets_under_test)
                                    netlist.append(net(pin, isundertest, netid))
                                    netlist[-1].connections.append([device_name, PASSIVE_PORTS[i]])
                                    netid = netid + 1
                        elif line.strip().startswith("x"):
                            pass
                        elif line.strip().startswith(".ends") or line.strip().startswith(".END"):
                            netlist.sort(key=lambda x: x.name)
                            subcircuit_list.append(subcircuit(subcircuit_name, portlist, netlist, subcircuit_id))
                            subcircuit_id = subcircuit_id + 1
                            logging.info("{}" .format(subcircuit_list[-1]))
                        else:
                            pass
    return subcircuit_list

def get_net_position(net, netlist):
    temp_pos = [i for i, x in enumerate(netlist) if x==net]
    return TRANSISTOR_PORTS[temp_pos[0]]

    breakpoint()

def add_parasitics(WORK_DIR, design, subcircuit_list):
    spicefile = design + ".sp"
    includefile = design + "_parasitics.inc"
    spicefile_with_parasitics = design + "_with_parasitics.sp"
    paramfile = design + "_params.inc"
    tc_directory = "/" + design + "/"
    netlist_with_parasitics = ".include \"" + paramfile + "\"\n"
    param_name_list = list()
    param_list = list()
    parasitic_str = ""
    param_str = ".param rpu = 30\n.param cpu = 2e-16\n"
    logging.info("Adding parasitics: {}" .format(spicefile))
    with open(WORK_DIR + tc_directory + "nets_under_test.txt", "r") as fnode:
        for line in fnode:
            nets_under_test = line.strip().split()

    with open(WORK_DIR + tc_directory + spicefile, "r") as fspice:
        for line in fspice:
            line = line.strip()
            if not line.startswith("//"):
                if line.startswith(".subckt"):
                    netlist_with_parasitics = netlist_with_parasitics + line + "\n"
                elif line.startswith(".end") or line.startswith(".END"):
                    netlist_with_parasitics = netlist_with_parasitics + parasitic_str
                    netlist_with_parasitics = netlist_with_parasitics + line + "\n"
                else:
                    if line.startswith("m") or line.startswith("M"):
                        list_from_line = line.split()
                        device_name = list_from_line[0]
                        net_names = list_from_line[1:5]
                        set_from_net_names = set(net_names)
                        device_desc = list_from_line[5:]

                        for net in set_from_net_names:
                            if net in nets_under_test:
                                temp_pin = get_net_position(net, net_names)
                                net_to_device = net + "_" + device_name
                                net_names[net_names.index(net)] = net_to_device
                                net_names = [net_to_device if item == net else item for item in net_names]
                                # print(net_names.index(net))
                                # print(net_names[net_names.index(net)])
                                parasitic_str = parasitic_str + "RP_" + net_to_device + " " \
                                            + net + " " + net_to_device + " resistor r = rpu*" \
                                            + "rp_" + net_to_device + "\n"
                                parasitic_str = parasitic_str + "CP_" + net_to_device + " " \
                                            + net_to_device + " " + "vss" + " capacitor c = cpu*" \
                                            + "cp_" + net_to_device + "\n"
                                param_str = param_str + ".param " + "rp_" + net_to_device + " = 0.1" + "\n"
                                param_str = param_str + ".param " + "cp_" + net_to_device + " = 0.1" + "\n"
                                param_name_list.append("rp_" + net_to_device)
                                param_name_list.append("cp_" + net_to_device)
                                param_list.append(param("rp_" + net_to_device, temp_pin))
                                param_list.append(param("cp_" + net_to_device, temp_pin))
                        new_line = " ".join([device_name] + net_names + device_desc)
                        netlist_with_parasitics = netlist_with_parasitics +new_line + "\n"

    if not os.path.exists(WORK_DIR + tc_directory + "reworked_netlist"):
        os.mkdir(WORK_DIR + tc_directory + "reworked_netlist")

    with open(WORK_DIR + tc_directory + "reworked_netlist/" + spicefile_with_parasitics, "w") as fspicenew:
        fspicenew.write(netlist_with_parasitics)
    with open(WORK_DIR + tc_directory + "reworked_netlist/" + paramfile, "w") as fparam:
        fparam.write(param_str)

    return param_list, param_name_list

def add_parasitics_for_FN(WORK_DIR, design, subcircuit_list, TOTAL_SAMPLES):
    spicefile = design + ".sp"
    includefile = design + "_parasitics.inc"
    spicefile_with_parasitics = design + "_with_parasitics_for_ML.sp"
    paramfile = design + "_params.inc"
    tc_directory = "/" + design + "/"
    param_name_list = list()
    param_list = list()
    netlist_with_parasitics = ""
    parasitic_str = ""
    param_str = ".param rpu = 30\n.param cpu = 2e-16\n"
    logging.info("Adding parasitics: {}" .format(spicefile))

    netlist_with_parasitics = netlist_with_parasitics + "simulator lang = spectre\n"
    netlist_with_parasitics = netlist_with_parasitics + get_lhs_samples(WORK_DIR, design, TOTAL_SAMPLES)
    netlist_with_parasitics = netlist_with_parasitics + "simulator lang = spice\n"
    netlist_with_parasitics = netlist_with_parasitics + ".include \"" + paramfile + "\"\n"
    with open(WORK_DIR + tc_directory + "nets_under_test.txt", "r") as fnode:
        for line in fnode:
            nets_under_test = line.strip().split()

    with open(WORK_DIR + tc_directory + spicefile, "r") as fspice:
        for line in fspice:
            line = line.strip()
            if not line.startswith("//"):
                if line.startswith(".subckt"):
                    netlist_with_parasitics = netlist_with_parasitics + line + "\n"
                elif line.startswith(".end") or line.startswith(".END"):
                    netlist_with_parasitics = netlist_with_parasitics + parasitic_str
                    netlist_with_parasitics = netlist_with_parasitics + line + "\n"
                else:
                    if line.startswith("m") or line.startswith("M"):
                        list_from_line = line.split()
                        device_name = list_from_line[0]
                        net_names = list_from_line[1:5]
                        set_from_net_names = set(net_names)
                        device_desc = list_from_line[5:]

                        for net in set_from_net_names:
                            if net in nets_under_test:
                                net_to_device = net + "_" + device_name
                                net_names[net_names.index(net)] = net_to_device
                                net_names = [net_to_device if item == net else item for item in net_names]
                                # print(net_names.index(net))
                                # print(net_names[net_names.index(net)])
                                parasitic_str = parasitic_str + "RP_" + net_to_device + " " \
                                            + net + " " + net_to_device + " resistor r = rpu*" \
                                            + "rp_" + net_to_device + "\n"
                                parasitic_str = parasitic_str + "CP_" + net_to_device + " " \
                                            + net_to_device + " " + "vss" + " capacitor c = cpu*" \
                                            + "cp_" + net_to_device + "\n"
                                param_str = param_str + ".param " + "rp_" + net_to_device + " = 0.1" + "\n"
                                param_str = param_str + ".param " + "cp_" + net_to_device + " = 0.1" + "\n"
                                # param_name_list.append("rp_" + net_to_device)
                                # param_name_list.append("cp_" + net_to_device)
                                # param_list.append(param("rp_" + net_to_device))
                                # param_list.append(param("cp_" + net_to_device))
                        new_line = " ".join([device_name] + net_names + device_desc)
                        netlist_with_parasitics = netlist_with_parasitics +new_line + "\n"

    if not os.path.exists(WORK_DIR + tc_directory + "reworked_netlist"):
        os.mkdir(WORK_DIR + tc_directory + "reworked_netlist")

    with open(WORK_DIR + tc_directory + "reworked_netlist/" + spicefile_with_parasitics, "w") as fspicenew:
        fspicenew.write(netlist_with_parasitics)
    # with open(WORK_DIR + tc_directory + "reworked_netlist/" + paramfile, "w") as fparam:
    #     fparam.write(param_str)

    return param_list, param_name_list

def read_nets_under_test(WORK_DIR, design):
    with open(WORK_DIR + "/" + design +"/nets_under_test.txt","r") as f:
        for line in f:
            # print(line)
            nets_under_test = line.strip().split()
    return nets_under_test

def extract_netlist(WORK_DIR, design, nodes_under_test,device_type_set):
    inputfile = design + ".sp"
    infile_revised = design + "_revised.sp"
    revised_netlist = ""

    device_list = list()
    node_list = list()

    if not os.path.exists(WORK_DIR + "/inputs/reworked_netlist"):
        os.mkdir(WORK_DIR + "/inputs/reworked_netlist")

    # nodes_under_test = read_nodes_under_test(WORK_DIR)
    with open(WORK_DIR + "/inputs/" + inputfile, "r") as finput, \
         open(WORK_DIR + "/inputs/reworked_netlist/" + infile_revised, "w") as fnew:
        for line in finput:
            # print(line)
            line = line.lstrip()
            if not line.startswith("//"):
                if line.startswith("global" or ".global"):
                    for item in line.split()[1:]:
                        node_list.append(node(item, "global", nodes_under_test))
                        if node_list[-1].alias != None:
                            line = re.sub(r"\s+" + node_list[-1].name + r"\s+", " "+node_list[-1].alias+" ",line)
                        line = line + "\n"
                elif line.startswith("subckt " or ".subckt"):
                    # print(line)
                    revised_netlist = revised_netlist + line
                    device_type_set.add(line.split()[1])
                    # print(device_type_set)
                    for line in finput:
                        if line.startswith("ends" or ".ends"):
                            break
                        else:
                            revised_netlist = revised_netlist + line
                            pass
                else:
                    for num,item in enumerate(line.split()):
                        if item in device_type_set:
                            dev_desc = " ".join(line.split()[:num+1])
                            others = " ".join(line.split()[num+1:])
                            device_list.append(device(dev_desc,nodes_under_test,node_list,device_type_set))
                            dev_desc = dev_desc.replace('(',' ').replace(')',' ')
                            for nodes in device_list[-1].nodelist:
                                if nodes.name.isnumeric():
                                    dev_desc = re.sub(r'(?<=\s)'+nodes.name+" "," "+nodes.alias+" ",dev_desc)
                            line = dev_desc + ' ' + others + '\n'
                            break
            revised_netlist = revised_netlist + line
        fnew.write(revised_netlist)
    return device_list, node_list

def add_parasitics_for_FSP(WORK_DIR, design, device_list, node_list):
    # global param_list
    infile_revised = design + "_revised.sp"
    infile_final = design + "_final.sp"
    parasiticfile = design + ".inc"
    param_list = []
    param_name_list = []
    ffinal = ""
    fparasitic = ""
    temp = ""
    temp = temp + "parameters rpu = 30\n"
    temp = temp + "parameters cpu = 5e-16\n"
    # global var_count
    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_revised,"r") as frevised:
        for line in frevised:
            for dev in device_list:
                if line.startswith(dev.name+" "):
                    for node in dev.nodelist:
                        if node.isundertest == True:
                            # var_count = var_count + 1
                            if node.name.isnumeric():
                                # line = re.sub(" "+node.alias+" "," "+node.alias+"_"+dev.name+" ",line)
                                if len(node.devlist) == 2:
                                    # print("Here it is!")
                                    if "rp_"+node.alias not in param_name_list:
                                        temp = temp + "parameters rp_"+node.alias+" = 0\n"
                                        param_name_list.append("rp_"+node.alias)
                                        param_list.append(param("rp_"+node.alias))
                                    if "cp_"+node.alias not in param_name_list:
                                        temp = temp + "parameters cp_"+node.alias+" = 0\n"
                                        param_name_list.append("cp_"+node.alias)
                                        param_list.append(param("cp_"+node.alias))
                                else:
                                    # print("Nope.")
                                    temp = temp + "parameters rp_"+node.alias+'_'+dev.name+" = 0\n"
                                    param_name_list.append("rp_"+node.alias+'_'+dev.name)
                                    param_list.append(param("rp_"+node.alias+'_'+dev.name))
                                    temp = temp + "parameters cp_"+node.alias+'_'+dev.name+" = 0\n"
                                    param_name_list.append("cp_"+node.alias+'_'+dev.name)
                                    param_list.append(param("cp_"+node.alias+'_'+dev.name))
                            else:
                                if len(node.devlist) == 2:
                                    # print("Here it is!")
                                    if "rp_"+node.name not in param_name_list:
                                        temp = temp + "parameters rp_"+node.name+" = 0\n"
                                        param_name_list.append("rp_"+node.name)
                                        param_list.append(param("rp_"+node.name))
                                    if "cp_"+node.name not in param_name_list:
                                        temp = temp + "parameters cp_"+node.name+" = 0\n"
                                        param_name_list.append("cp_"+node.name)
                                        param_list.append(param("cp_"+node.name))
                                else:
                                    # print("Nope.")
                                # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
                                    temp = temp + "parameters rp_"+node.name+'_'+dev.name+" = 0\n"
                                    param_name_list.append("rp_"+node.name+'_'+dev.name)
                                    param_list.append(param("rp_"+node.name+'_'+dev.name))
                                    temp = temp + "parameters cp_"+node.name+'_'+dev.name+" = 0\n"
                                    param_name_list.append("cp_"+node.name+'_'+dev.name)
                                    param_list.append(param("cp_"+node.name+'_'+dev.name))

    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_revised,"r") as frevised, open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,"w") as fnew:
        for line in frevised:
            if line.startswith("global"):
                line = line + "\n" + temp
            for dev in device_list:
                if line.startswith(dev.name+" "):
                    for node in dev.nodelist:
                        if node.isundertest == True:
                            if node.name.isnumeric():
                                if len(node.devlist) == 2:
                                    # line = re.sub(" "+node.alias+" "," "+node.alias+"_"+dev.name+" ",line)
                                    line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                    fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'*rpu/2\n'
                                    fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'*cpu/2\n'
                                else:
                                    line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                    fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'_'+dev.name+'*rpu\n'
                                    fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'_'+dev.name+'*cpu\n'
                            else:
                                if len(node.devlist) == 2:
                                # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
                                    line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                    fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'*rpu/2\n'
                                    fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'*cpu/2\n'
                                else:
                                    line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                    fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'_'+dev.name+'*rpu\n'
                                    fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'_'+dev.name+'*cpu\n'
            ffinal = ffinal + line
        ffinal = ffinal + "\n" + "include \"" + parasiticfile + "\""
        fnew.write(ffinal)

    with open(WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile,"w") as fpar:
        # print(fparasitic)
        fpar.write(fparasitic)
    return param_list, param_name_list

def extract_mdl(WORK_DIR, design, simcode):
    logging.info("Extracting MDL files...")
    tc_directory = "/" + design + "/"
    mdlfile = design + ".mdl"
    mdlfile_ac_2 = design +"_ac_2.mdl"
    mdlfile_ac_3 = design +"_ac_3.mdl"
    mdlfile_dc_1 = design +"_dc_1.mdl"
    mdlfile_dc_2 = design +"_dc_2.mdl"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    parasiticfile = design + "_params.inc"
    netlistfile = design + "_with_parasitics.sp"
    tbfile = design + "_tb_new.sp"
    simulation_list = list()
    spec_list_ac_1 = list()
    spec_list_dc_1 = list()
    spec_list_ac_2 = list()
    spec_list_ac_3 = list()
    spec_list_tran_1 = list()
    spec_csv = pd.read_csv(WORK_DIR + tc_directory + "spec_limits.csv")

    if not os.path.exists(WORK_DIR + tc_directory + "sims"):
        os.mkdir(WORK_DIR + tc_directory + "sims")

    if int(simcode[0])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/" + mdlfile):
        is_in_measurement = False
        simulation_list.append(simulation("ac_1"))

        with open (WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile,"r") as fmdl:
            logging.info("Extracting {}" .format(mdlfile))
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        x = re.search("step(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                        simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                        simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                        temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                        simulation_list[-1].count.append(temp)
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_1"):
            os.mkdir(WORK_DIR + tc_directory +"sims/outputs_ac_1")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile+" "+WORK_DIR + tc_directory +"sims/outputs_ac_1/"+mdlfile)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_ac_1/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_1/"+netlistfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_1/"+tbfile)
        # print(spec_list_ac_1)
        # return spec_list_ac_1
    else:
        logging.info("Ignoring ac1. Either mdl file does not exist or, simulation is not needed.")
    #
    if int(simcode[3])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/" + mdlfile_dc_1):
        logging.info("Extracting {}" .format(mdlfile))
        is_in_measurement = False
        simulation_list.append(simulation("dc_1"))
        with open(WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_dc_1,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        x = re.search("step(\s+)?=(\s+)?(\d+.)?\d+",line)
                        y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                        simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                        simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                        temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                        simulation_list[-1].count.append(temp)
                        line = next(fmdl) # to bypass 2nd for loop. Hard-coded.
                        if line.lstrip().startswith("foreach"):
                            x = re.search("step(\s+)?=(\s+)?(\d+.)?\d+",line)
                            y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                            z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                            simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                            simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                            simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                            temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                            simulation_list[-1].count.append(temp)
                else:
                    if line.startswith("export"):
                        spec_list_dc_1.append(line.split()[2])
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_dc_1"):
            os.mkdir(WORK_DIR + tc_directory +"sims/outputs_dc_1")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_dc_1 +" "+WORK_DIR + tc_directory +"sims/outputs_dc_1/"+mdlfile_dc_1)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_dc_1/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_dc_1/"+netlistfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_dc_1/"+tbfile)
    else:
        logging.info("Ignoring dc1. Either mdl file does not exist or, simulation is not needed.")

    if int(simcode[4])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/" + mdlfile_tran_1):
        is_in_measurement = False
        simulation_list.append(simulation("tran_1"))

        with open(WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_tran_1,"r") as fmdl:
            for line in fmdl:
                # print(line)
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        x = re.search("step(\s+)?=(\s+)?(\d+.)?\d+",line)
                        y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                        simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                        simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                        temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                        simulation_list[-1].count.append(temp)
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_tran_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False
    else:
        logging.info("Ignoring tran1. Either mdl file does not exist or, simulation is not needed.")
        # print(spec_list_tran_1[-1].name)
        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_tran_1"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_tran_1")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_tran_1 +" "+WORK_DIR + tc_directory +"sims/outputs_tran_1/"+mdlfile_tran_1)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_tran_1/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_tran_1/"+netlistfile)
        # os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_tran_1/"+tbfile)
        modify_spice_file_for_tran_sim(WORK_DIR, design, tbfile)

    if int(simcode[1])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_ac_2):
        is_in_measurement = False
        simulation_list.append(simulation("ac_2"))

        with open (WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_ac_2,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        x = re.search("step(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                        simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                        simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                        temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                        simulation_list[-1].count.append(temp)
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_2.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_2"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_ac_2")
        os.system("cp "+WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_ac_2+" "+WORK_DIR + tc_directory + "sims/outputs_ac_2/"+mdlfile_ac_2)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+parasiticfile+" "+WORK_DIR + tc_directory + "sims/outputs_ac_2/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_2/"+netlistfile)
        modify_spice_file_for_ac_2_sim(WORK_DIR, design, tbfile)
    else:
        logging.info("Ignoring ac2. Either mdl file does not exist or, simulation is not needed.")
    #
    if int(simcode[2])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_ac_3):
        is_in_measurement = False
        simulation_list.append(simulation("ac_3"))

        with open (WORK_DIR + tc_directory +"MDLforFSP/"+mdlfile_ac_3,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        x = re.search("step(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        y = re.search("stop(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        z = re.search("start(\s+)?=(\s+)?(\d+)?(.\d+)?",line)
                        simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
                        simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
                        simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
                        temp = round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1
                        simulation_list[-1].count.append(temp)
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_3.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_3"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_ac_3")
        os.system("cp "+WORK_DIR + tc_directory + "MDLforFSP/"+mdlfile_ac_3+" "+WORK_DIR + tc_directory +"sims/outputs_ac_3/"+mdlfile_ac_3)
        os.system("cp "+WORK_DIR + tc_directory + "reworked_netlist/"+parasiticfile+" "+WORK_DIR + tc_directory +"sims/outputs_ac_3/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_3/"+netlistfile)
        modify_spice_file_for_ac_3_sim(WORK_DIR, design, tbfile)
    else:
        logging.info("Ignoring ac3. Either mdl file does not exist or, simulation is not needed.")
    return spec_list_ac_1,spec_list_ac_2,spec_list_ac_3,spec_list_dc_1,spec_list_tran_1,simulation_list

def modify_spice_file_for_tran_sim(WORK_DIR, design, infile_final):
    temp = ""
    tc_directory = "/" + design + "/"
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_tran_1/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v7"):
                temp = temp + "v7 n101  0 vsource dc=vcm_r mag=0 type=dc" + '\n'
                # temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.1 3135.06e-12 -0.1 3145.06e-12 0.1]" + '\n'
#                temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.165 5036.10e-12 -0.15 5046.10e-12 0.165]" + '\n'
                temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.075 5036.10e-12 -0.075 5046.10e-12 0.075]" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  0 vsource dc=vcm_r mag=0 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass

def modify_spice_file_for_ac_2_sim(WORK_DIR, design, infile_final):
    temp = ""
    tc_directory = "/" + design + "/"
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_ac_2/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v7"):
                temp = temp + "v7 n10  0 vsource dc=vcm_r+0.001 mag=0.5 type=dc" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  0 vsource dc=vcm_r mag=0.5 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass

def modify_spice_file_for_ac_3_sim(WORK_DIR, design, infile_final):
    temp = ""
    tc_directory = "/" + design + "/"
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_ac_3/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v4"):
                temp = temp + "v4 VDD 0 vsource dc=vdd_r mag=1 type=dc" + '\n'
            elif line.startswith("v7"):
                temp = temp + "v7 n10  0 vsource dc=vcm_r+0.001 mag=0 type=dc" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  0 vsource dc=vcm_r mag=0 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass


# def add_parasitics_for_FN(WORK_DIR, design, device_list, node_list, TOTAL_SAMPLES):
#     # global param_list
#     infile_revised = design + "_revised.sp"
#     infile_final = design + "_for_FT.sp"
#     parasiticfile = design + "_for_FT.inc"
#     param_list = []
#     param_name_list = []
#     ffinal = ""
#     fparasitic = ""
#     temp = ""
#     temp = temp + "parameters rpu = 30\n"
#     temp = temp + "parameters cpu = 5e-16\n"
#     if os.path.exists(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv"):
#         # logging.info("Reading node to device parasitics that are under consideration...")
#         df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
#         param_under_test = df_bounds.columns.tolist()
#         print(param_under_test)
#     else:
#         # logging.error("The file node_under_test_for_smartforce.csv is not available.")
#         exit()
#     with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_revised,"r") as frevised:
#         for line in frevised:
#             for dev in device_list:
#                 if line.startswith(dev.name+" "):
#                     for node in dev.nodelist:
#                         if node.isundertest == True:
#                             # var_count = var_count + 1
#                             if node.name.isnumeric():
#                                 # line = re.sub(" "+node.alias+" "," "+node.alias+"_"+dev.name+" ",line)
#                                 if len(node.devlist) == 2:
#                                     # print("Here it is!")
#                                     if "rp_"+node.alias in param_under_test:
#                                         if "rp_"+node.alias not in param_list:
#                                             temp = temp + "parameters rp_"+node.alias+" = 0\n"
#                                             # param_name_list.append("rp_"+node.alias)
#                                             param_list.append("rp_"+node.alias)
#                                     if "cp_"+node.alias in param_under_test:
#                                         if "cp_"+node.alias not in param_list:
#                                             temp = temp + "parameters cp_"+node.alias+" = 0\n"
#                                             # param_name_list.append("cp_"+node.alias)
#                                             param_list.append("cp_"+node.alias)
#                                 else:
#                                     # print("Nope.")
#                                     if "rp_"+node.alias+'_'+dev.name in param_under_test:
#                                         temp = temp + "parameters rp_"+node.alias+'_'+dev.name+" = 0\n"
#                                         # param_name_list.append("rp_"+node.alias+'_'+dev.name)
#                                         param_list.append("rp_"+node.alias+'_'+dev.name)
#                                     if "cp_"+node.alias+'_'+dev.name in param_under_test:
#                                         temp = temp + "parameters cp_"+node.alias+'_'+dev.name+" = 0\n"
#                                         # param_name_list.append("cp_"+node.alias+'_'+dev.name)
#                                         param_list.append("cp_"+node.alias+'_'+dev.name)
#                             else:
#                                 if len(node.devlist) == 2:
#                                     # print("Here it is!")
#                                     if "rp_"+node.name in param_under_test:
#                                         if "rp_"+node.name not in param_list:
#                                             temp = temp + "parameters rp_"+node.name+" = 0\n"
#                                             # param_name_list.append("rp_"+node.name)
#                                             param_list.append("rp_"+node.name)
#                                     if "cp_"+node.name in param_under_test:
#                                         if "cp_"+node.name not in param_list:
#                                             temp = temp + "parameters cp_"+node.name+" = 0\n"
#                                             # param_name_list.append("cp_"+node.name)
#                                             param_list.append("cp_"+node.name)
#                                 else:
#                                     # print("Nope.")
#                                 # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
#                                     if "rp_"+node.name+'_'+dev.name in param_under_test:
#                                         temp = temp + "parameters rp_"+node.name+'_'+dev.name+" = 0\n"
#                                         # param_name_list.append("rp_"+node.name+'_'+dev.name)
#                                         param_list.append("rp_"+node.name+'_'+dev.name)
#                                     if "cp_"+node.name+'_'+dev.name in param_under_test:
#                                         temp = temp + "parameters cp_"+node.name+'_'+dev.name+" = 0\n"
#                                         # param_name_list.append("cp_"+node.name+'_'+dev.name)
#                                         param_list.append("cp_"+node.name+'_'+dev.name)
#
#     temp = temp + get_lhs_samples(WORK_DIR, TOTAL_SAMPLES)
#
#     with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_revised,"r") as frevised, open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,"w") as fnew:
#         for line in frevised:
#             if line.startswith("global"):
#                 line = line + "\n" + temp
#             for dev in device_list:
#                 if line.startswith(dev.name+" "):
#                     for node in dev.nodelist:
#                         if node.isundertest == True:
#                             if node.name.isnumeric():
#                                 if len(node.devlist) == 2:
#                                     # line = re.sub(" "+node.alias+" "," "+node.alias+"_"+dev.name+" ",line)
#                                     #line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                     if "rp_"+node.alias in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                         fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'*rpu/2\n'
#                                     if "cp_"+node.alias in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                         fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'*cpu/2\n'
#                                 else:
#                                     # line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                     if "rp_"+node.alias+'_'+dev.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                         fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'_'+dev.name+'*rpu\n'
#                                     if "cp_"+node.alias+'_'+dev.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
#                                         fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'_'+dev.name+'*cpu\n'
#                             else:
#                                 if len(node.devlist) == 2:
#                                 # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
#                                     # line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                     if "rp_"+node.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                         fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'*rpu/2\n'
#                                     if "cp_"+node.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                         fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'*cpu/2\n'
#                                 else:
#                                     # line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                     if "rp_"+node.name+'_'+dev.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                         fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'_'+dev.name+'*rpu\n'
#                                     if "cp_"+node.name+'_'+dev.name in param_under_test:
#                                         line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
#                                         fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'_'+dev.name+'*cpu\n'
#             ffinal = ffinal + line
#         ffinal = ffinal + "\n" + "include \"" + parasiticfile + "\""
#         fnew.write(ffinal)
#
#     with open(WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile,"w") as fpar:
#         # print(fparasitic)
#         fpar.write(fparasitic)
#     return param_list

def gen_constraints(WORK_DIR, design_name, param_list):
    verilogfile = design_name + ".v"
    device_list = []
    net_list = []
    parasitic_list = []
    constraint_list = []
    slist = ['module','endmodule','input','`celldefine','`endcelldefine', 'supply0', 'supply1']
    for item in param_list:
        temp = item.split('_')
        parasitic_list.append(temp[0])
        net_list.append(temp[1])
        device_list.append(temp[2])
        pass

    # print(device_list)
    # print(net_list)
    # print(parasitic_list)

    with open(WORK_DIR+"/inputs/"+verilogfile,"r") as fverilog:
        for line_verilog in fverilog:
            if not line_verilog.startswith("//"):
                temp = line_verilog.strip().split()
                if temp:
                    # print(line_verilog)
                    if temp[0] not in slist:
                        # print("temp[0]: {}".format(temp[0]))
                        # print("temp[1]: {}".format(temp[1]))
                        # print(device_list)
                        if temp[1] in device_list:
                            # print("temp[0]: {}, temp[1]: {}".format(temp[0],temp[1]))
                            for i, node in enumerate(temp):
                                if i > 2 and i < len(temp)-1:
                                    net = node.strip('.),').split('(')
                                    # print("{} {}".format(net[0],net[1]))
                                    for j, item in enumerate(net_list):
                                        if net[1]==item and net[0]!="B" and temp[1] == device_list[j]:
                                            # print("Device: {}, Net: {}, Node: {}, Type: {}".format(temp[1], net[1], net[0], parasitic_list[j]))
                                            constraint_list.append(net[1] + "/" + temp[1] + "/" + net[0] + "/" + parasitic_list[j][0])
    return ' , '.join(constraint_list)
