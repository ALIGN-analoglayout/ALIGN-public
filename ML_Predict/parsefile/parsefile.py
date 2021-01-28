import os
import re
import pandas as pd

from utils.classdesc import device,node,param,simulation,specs
from utils.utils import get_lhs_samples

# nodes_under_test = list()

def read_nodes_under_test(WORK_DIR):
    global nodes_under_test
    with open(WORK_DIR + "/inputs/node_under_test.txt","r") as f:
        for line in f:
            # print(line)
            nodes_under_test = line.strip().split()
    return nodes_under_test

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

def extract_mdl(WORK_DIR, design):
    mdlfile = design + ".mdl"
    mdlfile_ac_2 = design +"_ac_2.mdl"
    mdlfile_ac_3 = design +"_ac_3.mdl"
    mdlfile_dc_1 = design +"_dc_1.mdl"
    mdlfile_dc_2 = design +"_dc_2.mdl"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    parasiticfile = design + ".inc"
    infile_final = design + "_final.sp"
    simulation_list = list()
    spec_list_ac_1 = list()
    spec_list_dc_1 = list()
    spec_list_ac_2 = list()
    spec_list_ac_3 = list()
    spec_list_tran_1 = list()
    spec_csv = pd.read_csv(WORK_DIR+"/inputs/spec_limits.csv")
    if os.path.exists(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile):
        is_in_measurement = False
        simulation_list.append(simulation("ac_1"))

        with open (WORK_DIR+"/inputs/MDLforFSP/"+mdlfile,"r") as fmdl:
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

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_1"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_1")
        os.system("cp "+WORK_DIR+"/inputs/MDLforFSP/"+mdlfile+" "+WORK_DIR+"/sims/outputs_ac_1/"+mdlfile)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_1/"+parasiticfile)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+infile_final+" "+WORK_DIR+"/sims/outputs_ac_1/"+infile_final)

    if os.path.exists(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_dc_1):
        is_in_measurement = False
        simulation_list.append(simulation("dc_1"))
        with open(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_dc_1,"r") as fmdl:
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

        if not os.path.exists(WORK_DIR+"/sims/outputs_dc_1"):
            os.mkdir(WORK_DIR+"/sims/outputs_dc_1")
        os.system("cp "+WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_dc_1+" "+WORK_DIR+"/sims/outputs_dc_1/"+mdlfile_dc_1)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_dc_1/"+parasiticfile)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+infile_final+" "+WORK_DIR+"/sims/outputs_dc_1/"+infile_final)

    if os.path.exists(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_tran_1):
        is_in_measurement = False
        simulation_list.append(simulation("tran_1"))

        with open(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_tran_1,"r") as fmdl:
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

        # print(spec_list_tran_1[-1].name)
        if not os.path.exists(WORK_DIR+"/sims/outputs_tran_1"):
            os.mkdir(WORK_DIR+"/sims/outputs_tran_1")
        os.system("cp "+WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_tran_1+" "+WORK_DIR+"/sims/outputs_tran_1/"+mdlfile_tran_1)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_tran_1/"+parasiticfile)
        modify_spice_file_for_tran_sim(WORK_DIR,infile_final)
    #
    # if os.path.exists(WORK_DIR+"/inputs/"+mdlfile_dc_2):
    #     is_in_measurement = False
    #     simulation_list.append(simulation("dc_2"))
    #     with open(mdlfile_dc_2,"r") as fmdl:
    #         for line in fmdl:
    #             line = line.lstrip()
    #             if is_in_measurement == False:
    #                 if line.startswith("alias"):
    #                     is_in_measurement = True
    #                 elif line.startswith("foreach"):
    #                     x = re.search("step(\s+)?=(-)?(\s+)?(\d+.)?\d+",line)
    #                     y = re.search("stop(\s+)?=(-)?(\s+)?(\d+)?(.\d+)?",line)
    #                     z = re.search("start(\s+)?=(-)?(\s+)?(\d+)?(.\d+)?",line)
    #                     simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
    #                     simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
    #                     simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
    #                     temp = abs(round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1)
    #                     simulation_list[-1].count.append(temp)
    #                     line = next(fmdl) # to bypass 2nd for loop. Hard-coded.
    #                     if line.lstrip().startswith("foreach"):
    #                         x = re.search("step(\s+)?=(-)?(\s+)?(\d+.)?\d+",line)
    #                         y = re.search("stop(\s+)?=(-)?(\s+)?(\d+)?(.\d+)?",line)
    #                         z = re.search("start(\s+)?=(-)?(\s+)?(\d+)?(.\d+)?",line)
    #                         simulation_list[-1].step.append(x.group(0).split('=')[1].strip())
    #                         simulation_list[-1].stop.append(y.group(0).split('=')[1].strip())
    #                         simulation_list[-1].start.append(z.group(0).split('=')[1].strip())
    #                         temp = abs(round((float(simulation_list[-1].stop[-1]) - float(simulation_list[-1].start[-1]))/float(simulation_list[-1].step[-1])) + 1)
    #                         simulation_list[-1].count.append(temp)
    #             else:
    #                 if line.startswith("export"):
    #                     spec_list_dc_2.append(line.split()[2])
    #                 if line.rstrip().endswith("}"):
    #                     is_in_measurement = False
    #
    #     if not os.path.exists("outputs_dc_2"):
    #         os.mkdir("outputs_dc_2")
    #     os.system("cp "+mdlfile_dc_2+" "+"outputs_dc_2/"+mdlfile_dc_2)
    #     os.system("cp "+"./reworked_netlist/"+parasiticfile+" "+"outputs_dc_2/"+parasiticfile)
    #
    #     # modify_spice_file_for_dc_2_sim()
    #
    if os.path.exists(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_2):
        is_in_measurement = False
        simulation_list.append(simulation("ac_2"))

        with open (WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_2,"r") as fmdl:
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

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_2"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_2")
        os.system("cp "+WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_2+" "+WORK_DIR+"/sims/outputs_ac_2/"+mdlfile_ac_2)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_2/"+parasiticfile)    #
        modify_spice_file_for_ac_2_sim(WORK_DIR,infile_final)
    #
    if os.path.exists(WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_3):
        is_in_measurement = False
        simulation_list.append(simulation("ac_3"))

        with open (WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_3,"r") as fmdl:
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

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_3"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_3")
        os.system("cp "+WORK_DIR+"/inputs/MDLforFSP/"+mdlfile_ac_3+" "+WORK_DIR+"/sims/outputs_ac_3/"+mdlfile_ac_3)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_3/"+parasiticfile)
        modify_spice_file_for_ac_3_sim(WORK_DIR,infile_final)
    return spec_list_ac_1,spec_list_ac_2,spec_list_ac_3,spec_list_dc_1,spec_list_tran_1,simulation_list

def modify_spice_file_for_tran_sim(WORK_DIR,infile_final):
    temp = ""
    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_tran_1/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v7"):
                temp = temp + "v7 n101  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
                # temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.1 3135.06e-12 -0.1 3145.06e-12 0.1]" + '\n'
#                temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.165 5036.10e-12 -0.15 5046.10e-12 0.165]" + '\n'
                temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.075 5036.10e-12 -0.075 5046.10e-12 0.075]" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass

def modify_spice_file_for_ac_2_sim(WORK_DIR,infile_final):
    temp = ""

    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_ac_2/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v7"):
                temp = temp + "v7 n10  global_0 vsource dc=vcm_r+0.001 mag=0.5 type=dc" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  global_0 vsource dc=vcm_r mag=0.5 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass

def modify_spice_file_for_ac_3_sim(WORK_DIR,infile_final):
    temp = ""

    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_ac_3/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v4"):
                temp = temp + "v4 VDD global_0 vsource dc=vdd_r mag=1 type=dc" + '\n'
            elif line.startswith("v7"):
                temp = temp + "v7 n10  global_0 vsource dc=vcm_r+0.001 mag=0 type=dc" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass


def add_parasitics_for_FN(WORK_DIR, design, device_list, node_list, TOTAL_SAMPLES):
    # global param_list
    infile_revised = design + "_revised.sp"
    infile_final = design + "_for_FT.sp"
    parasiticfile = design + "_for_FT.inc"
    param_list = []
    param_name_list = []
    ffinal = ""
    fparasitic = ""
    temp = ""
    temp = temp + "parameters rpu = 30\n"
    temp = temp + "parameters cpu = 5e-16\n"
    if os.path.exists(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv"):
        # logging.info("Reading node to device parasitics that are under consideration...")
        df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
        param_under_test = df_bounds.columns.tolist()
        print(param_under_test)
    else:
        # logging.error("The file node_under_test_for_smartforce.csv is not available.")
        exit()
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
                                    if "rp_"+node.alias in param_under_test:
                                        if "rp_"+node.alias not in param_list:
                                            temp = temp + "parameters rp_"+node.alias+" = 0\n"
                                            # param_name_list.append("rp_"+node.alias)
                                            param_list.append("rp_"+node.alias)
                                    if "cp_"+node.alias in param_under_test:
                                        if "cp_"+node.alias not in param_list:
                                            temp = temp + "parameters cp_"+node.alias+" = 0\n"
                                            # param_name_list.append("cp_"+node.alias)
                                            param_list.append("cp_"+node.alias)
                                else:
                                    # print("Nope.")
                                    if "rp_"+node.alias+'_'+dev.name in param_under_test:
                                        temp = temp + "parameters rp_"+node.alias+'_'+dev.name+" = 0\n"
                                        # param_name_list.append("rp_"+node.alias+'_'+dev.name)
                                        param_list.append("rp_"+node.alias+'_'+dev.name)
                                    if "cp_"+node.alias+'_'+dev.name in param_under_test:
                                        temp = temp + "parameters cp_"+node.alias+'_'+dev.name+" = 0\n"
                                        # param_name_list.append("cp_"+node.alias+'_'+dev.name)
                                        param_list.append("cp_"+node.alias+'_'+dev.name)
                            else:
                                if len(node.devlist) == 2:
                                    # print("Here it is!")
                                    if "rp_"+node.name in param_under_test:
                                        if "rp_"+node.name not in param_list:
                                            temp = temp + "parameters rp_"+node.name+" = 0\n"
                                            # param_name_list.append("rp_"+node.name)
                                            param_list.append("rp_"+node.name)
                                    if "cp_"+node.name in param_under_test:
                                        if "cp_"+node.name not in param_list:
                                            temp = temp + "parameters cp_"+node.name+" = 0\n"
                                            # param_name_list.append("cp_"+node.name)
                                            param_list.append("cp_"+node.name)
                                else:
                                    # print("Nope.")
                                # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
                                    if "rp_"+node.name+'_'+dev.name in param_under_test:
                                        temp = temp + "parameters rp_"+node.name+'_'+dev.name+" = 0\n"
                                        # param_name_list.append("rp_"+node.name+'_'+dev.name)
                                        param_list.append("rp_"+node.name+'_'+dev.name)
                                    if "cp_"+node.name+'_'+dev.name in param_under_test:
                                        temp = temp + "parameters cp_"+node.name+'_'+dev.name+" = 0\n"
                                        # param_name_list.append("cp_"+node.name+'_'+dev.name)
                                        param_list.append("cp_"+node.name+'_'+dev.name)

    temp = temp + get_lhs_samples(WORK_DIR, TOTAL_SAMPLES)

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
                                    #line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                    if "rp_"+node.alias in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                        fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'*rpu/2\n'
                                    if "cp_"+node.alias in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                        fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'*cpu/2\n'
                                else:
                                    # line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                    if "rp_"+node.alias+'_'+dev.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                        fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.alias+" "+node.alias+" "+node.alias+"_"+dev.name+" resistor r = rp_"+node.alias+'_'+dev.name+'*rpu\n'
                                    if "cp_"+node.alias+'_'+dev.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.alias+r"(?=\s|$)",node.alias+"_"+dev.name,line)
                                        fparasitic = fparasitic + "CP_"+dev.name+"_"+node.alias+" "+node.alias+"_"+dev.name+" global_0 capacitor c = cp_"+node.alias+'_'+dev.name+'*cpu\n'
                            else:
                                if len(node.devlist) == 2:
                                # line = re.sub(" "+node.name+" "," "+node.name+"_"+dev.name+" ",line)
                                    # line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                    if "rp_"+node.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                        fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'*rpu/2\n'
                                    if "cp_"+node.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                        fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'*cpu/2\n'
                                else:
                                    # line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                    if "rp_"+node.name+'_'+dev.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                        fparasitic = fparasitic +  "RP_"+dev.name+"_"+node.name+" "+node.name+" "+node.name+"_"+dev.name+" resistor r = rp_"+node.name+'_'+dev.name+'*rpu\n'
                                    if "cp_"+node.name+'_'+dev.name in param_under_test:
                                        line = re.sub(r"(?:^|(?<=\s))"+node.name+r"(?=\s|$)",node.name+"_"+dev.name,line)
                                        fparasitic = fparasitic + "CP_"+dev.name+"_"+node.name+" "+node.name+"_"+dev.name+" global_0 capacitor c = cp_"+node.name+'_'+dev.name+'*cpu\n'
            ffinal = ffinal + line
        ffinal = ffinal + "\n" + "include \"" + parasiticfile + "\""
        fnew.write(ffinal)

    with open(WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile,"w") as fpar:
        # print(fparasitic)
        fpar.write(fparasitic)
    return param_list

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
