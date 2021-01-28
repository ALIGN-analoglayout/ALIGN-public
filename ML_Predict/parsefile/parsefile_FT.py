import os
import re
import pandas as pd

from utils.classdesc import device,node,param,simulation,specs

def extract_mdl_FT(WORK_DIR, design):
    mdlfile = design + ".mdl"
    mdlfile_ac_2 = design +"_ac_2.mdl"
    mdlfile_ac_3 = design +"_ac_3.mdl"
    mdlfile_dc_1 = design +"_dc_1.mdl"
    mdlfile_dc_2 = design +"_dc_2.mdl"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    parasiticfile = design + "_for_FT.inc"
    infile_final = design + "_for_FT.sp"
    simulation_list = list()
    spec_list_ac_1 = list()
    spec_list_dc_1 = list()
    spec_list_ac_2 = list()
    spec_list_ac_3 = list()
    spec_list_tran_1 = list()
    spec_csv = pd.read_csv(WORK_DIR + "/inputs/spec_limits.csv")
    if os.path.exists(WORK_DIR+"/inputs/MDLforML/"+mdlfile):
        is_in_measurement = False
        simulation_list.append(simulation("ac_1"))

        with open (WORK_DIR+"/inputs/MDLforML/"+mdlfile,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_1_FT"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_1_FT")
        os.system("cp "+WORK_DIR+"/inputs/MDLforML/"+mdlfile+" "+WORK_DIR+"/sims/outputs_ac_1_FT/"+mdlfile)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+infile_final+" "+WORK_DIR+"/sims/outputs_ac_1_FT/"+infile_final)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_1_FT/"+parasiticfile)

    if os.path.exists(WORK_DIR+"/inputs/MDLforML/"+mdlfile_dc_1):
        is_in_measurement = False
        simulation_list.append(simulation("ac_1"))
        with open(WORK_DIR+"/inputs/MDLforML/"+mdlfile_dc_1,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                else:
                    if line.startswith("export"):
                        spec_list_dc_1.append(line.split()[2])
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False
#
#         if not os.path.exists("outputs_dc_1"):
#             os.mkdir("outputs_dc_1")
#         os.system("cp "+mdlfile_dc_1+" "+"outputs_dc_1/"+mdlfile_dc_1)
#         os.system("cp "+"./reworked_netlist/"+parasiticfile+" "+"outputs_dc_1/"+parasiticfile)
#
        if not os.path.exists(WORK_DIR+"/sims/outputs_dc_1_FT"):
            os.mkdir(WORK_DIR+"/sims/outputs_dc_1_FT")
        os.system("cp "+WORK_DIR+"/inputs/MDLforML/"+mdlfile_dc_1+" "+WORK_DIR+"/sims/outputs_dc_1_FT/"+mdlfile_dc_1)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+infile_final+" "+WORK_DIR+"/sims/outputs_dc_1_FT/"+infile_final)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_dc_1_FT/"+parasiticfile)

    if os.path.exists(WORK_DIR+"/inputs/MDLforML/"+mdlfile_tran_1):
        is_in_measurement = False
        simulation_list.append(simulation("tran_1"))

        with open(WORK_DIR+"/inputs/MDLforML/"+mdlfile_tran_1,"r") as fmdl:
            for line in fmdl:
                # print(line)
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_tran_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR+"/sims/outputs_tran_1_FT"):
            os.mkdir(WORK_DIR+"/sims/outputs_tran_1_FT")
        os.system("cp -f "+WORK_DIR+"/inputs/MDLforML/"+mdlfile_tran_1+" "+WORK_DIR+"/sims/outputs_tran_1_FT/"+mdlfile_tran_1)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_tran_1_FT/"+parasiticfile)
        modify_spice_file_for_tran_sim(WORK_DIR, infile_final)
#
#     if os.path.exists(mdlfile_dc_2):
#         is_in_measurement = False
#         simulation_list.append(simulation("dc_2"))
#         with open(mdlfile_dc_2,"r") as fmdl:
#             for line in fmdl:
#                 line = line.lstrip()
#                 if is_in_measurement == False:
#                     if line.startswith("alias"):
#                         is_in_measurement = True
#                 else:
#                     if line.startswith("export"):
#                         spec_list_dc_2.append(line.split()[2])
#                     if line.rstrip().endswith("}"):
#                         is_in_measurement = False
#
#         if not os.path.exists("outputs_dc_2"):
#             os.mkdir("outputs_dc_2")
#         os.system("cp "+mdlfile_dc_2+" "+"outputs_dc_2/"+mdlfile_dc_2)
#         os.system("cp "+"./reworked_netlist/"+parasiticfile+" "+"outputs_dc_2/"+parasiticfile)
#
#         # modify_spice_file_for_dc_2_sim()
#
    if os.path.exists(WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_2):
        is_in_measurement = False
        simulation_list.append(simulation("ac_2"))

        with open (WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_2,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_2.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_2_FT"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_2_FT")
        os.system("cp "+WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_2+" "+WORK_DIR+"/sims/outputs_ac_2_FT/"+mdlfile_ac_2)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_2_FT/"+parasiticfile)
        modify_spice_file_for_ac_2_sim(WORK_DIR, infile_final)

    if os.path.exists(WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_3):
        is_in_measurement = False
        simulation_list.append(simulation("ac_3"))

        with open (WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_3,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    else:
                        pass
                else:
                    if line.startswith("export"):
                        spec_list_ac_3.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR+"/sims/outputs_ac_3_FT"):
            os.mkdir(WORK_DIR+"/sims/outputs_ac_3_FT")
        os.system("cp "+WORK_DIR+"/inputs/MDLforML/"+mdlfile_ac_3+" "+WORK_DIR+"/sims/outputs_ac_3_FT/"+mdlfile_ac_3)
        os.system("cp "+WORK_DIR+"/inputs/reworked_netlist/"+parasiticfile+" "+WORK_DIR+"/sims/outputs_ac_3_FT/"+parasiticfile)

        modify_spice_file_for_ac_3_sim(WORK_DIR, infile_final)
#
# def modify_spice_file_for_dc_2_sim():
#     temp = ""
#
#     with open("reworked_netlist/"+infile_final,'r') as fin, open("outputs_dc_2/"+infile_final,'w') as fout:
#         for line in fin:
#             line = line.strip()
#             if line.startswith("v7"):
#                 temp = temp + "v7 vinp1  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
#                 temp = temp + "v8 vinp1 vinp vsource dc=vdiff type=dc" + '\n'
#             elif line.startswith("v6"):
#                 temp = temp + "v6 vinn1  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
#                 temp = temp + "v9 vinn1 vinn vsource dc=-vdiff type=dc" + '\n'
#             else:
#                 temp = temp + line + '\n'
#         fout.write(temp)
#     pass
#
def modify_spice_file_for_tran_sim(WORK_DIR, infile_final):
    temp = ""
    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_tran_1_FT/"+infile_final,'w') as fout:
        for line in fin:
            line = line.strip()
            if line.startswith("v7"):
                temp = temp + "v7 n101  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
                temp = temp + "v8 n101 n10 vsource type=pwl wave=[0 0 100e-12 0 110e-12 -0.075 5036.10e-12 -0.075 5046.10e-12 0.075]" + '\n'
            elif line.startswith("v6"):
                temp = temp + "v6 n9  global_0 vsource dc=vcm_r mag=0 type=dc" + '\n'
            else:
                temp = temp + line + '\n'
        fout.write(temp)
    pass
#
def modify_spice_file_for_ac_2_sim(WORK_DIR, infile_final):
    temp = ""

    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_ac_2_FT/"+infile_final,'w') as fout:
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
#
def modify_spice_file_for_ac_3_sim(WORK_DIR, infile_final):
    temp = ""

    with open(WORK_DIR+"/inputs/reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR+"/sims/outputs_ac_3_FT/"+infile_final,'w') as fout:
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
