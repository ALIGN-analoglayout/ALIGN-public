import os
import re
import pandas as pd
import logging

from utils.classdesc import device,node,param,simulation,specs

def extract_mdl_FT(WORK_DIR, simcode, design):
    logging.info("Extracting MDL for FT...")
    tc_directory = "/" + design + "/"
    mdlfile = design + ".mdl"
    mdlfile_ac_2 = design +"_ac_2.mdl"
    mdlfile_ac_3 = design +"_ac_3.mdl"
    mdlfile_dc_1 = design +"_dc_1.mdl"
    mdlfile_dc_2 = design +"_dc_2.mdl"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    parasiticfile = design + "_params.inc"
    netlistfile = design + "_with_parasitics_for_ML.sp"
    tbfile = design + "_tb_new_for_ML.sp"
    simulation_list = list()
    spec_list_ac_1 = list()
    spec_list_dc_1 = list()
    spec_list_ac_2 = list()
    spec_list_ac_3 = list()
    spec_list_tran_1 = list()
    spec_csv = pd.read_csv(WORK_DIR + tc_directory + "spec_limits.csv")

    # if not os.path.exists(WORK_DIR + tc_directory + "sims"):
    #     os.mkdir(WORK_DIR + tc_directory + "sims")

    if int(simcode[0])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + mdlfile):
        is_in_measurement = False
        simulation_list.append(simulation("ac_1"))

        with open (WORK_DIR + tc_directory + "MDLforML/"+mdlfile,"r") as fmdl:
            logging.info("Extracting {}" .format(mdlfile))
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        pass
                    else:
                        pass
                else:
                    # if line.startswith("export"):
                    #     spec_list_ac_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_1_FT"):
            os.mkdir(WORK_DIR + tc_directory +"sims/outputs_ac_1_FT")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforML/"+mdlfile+" "+WORK_DIR + tc_directory +"sims/outputs_ac_1_FT/"+mdlfile)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_ac_1_FT/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_1_FT/"+netlistfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_1_FT/"+tbfile)
    else:
        logging.info("Ignoring ac1. Either mdl file does not exist or, simulation is not needed.")
        # print(spec_list_ac_1)
        # return spec_list_ac_1
    #
    if int(simcode[3])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + mdlfile_dc_1):
        logging.info("Extracting {}" .format(mdlfile))
        is_in_measurement = False
        simulation_list.append(simulation("dc_1"))
        with open(WORK_DIR + tc_directory + "MDLforML/"+mdlfile_dc_1,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        pass
                else:
                    # if line.startswith("export"):
                    #     spec_list_dc_1.append(line.split()[2])
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_dc_1_FT"):
            os.mkdir(WORK_DIR + tc_directory +"sims/outputs_dc_1_FT")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforML/"+mdlfile_dc_1 +" "+WORK_DIR + tc_directory +"sims/outputs_dc_1_FT/"+mdlfile_dc_1)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_dc_1_FT/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_dc_1_FT/"+netlistfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_dc_1_FT/"+tbfile)
    else:
        logging.info("Ignoring dc1. Either mdl file does not exist or, simulation is not needed.")

    if int(simcode[4])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + mdlfile_tran_1):
        is_in_measurement = False
        simulation_list.append(simulation("tran_1"))

        with open(WORK_DIR + tc_directory + "MDLforML/"+mdlfile_tran_1,"r") as fmdl:
            for line in fmdl:
                # print(line)
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        pass
                    else:
                        pass
                else:
                    # if line.startswith("export"):
                        # spec_list_tran_1.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        # print(spec_list_tran_1[-1].name)
        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_tran_1_FT"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_tran_1_FT")
        os.system("cp " + WORK_DIR + tc_directory + "MDLforML/"+mdlfile_tran_1 +" "+WORK_DIR + tc_directory +"sims/outputs_tran_1_FT/"+mdlfile_tran_1)
        os.system("cp "+WORK_DIR + tc_directory  +"reworked_netlist/"+parasiticfile+" "+ WORK_DIR + tc_directory + "sims/outputs_tran_1_FT/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_tran_1_FT/"+netlistfile)
        # os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+tbfile+" "+ WORK_DIR + tc_directory +"sims/outputs_tran_1/"+tbfile)
        modify_spice_file_for_tran_sim(WORK_DIR, design, tbfile)
    else:
        logging.info("Ignoring tran1. Either mdl file does not exist or, simulation is not needed.")

    if int(simcode[1])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforML/"+mdlfile_ac_2):
        is_in_measurement = False
        simulation_list.append(simulation("ac_2"))

        with open (WORK_DIR + tc_directory + "MDLforML/"+mdlfile_ac_2,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        pass
                    else:
                        pass
                else:
                    # if line.startswith("export"):
                        # spec_list_ac_2.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_2_FT"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_ac_2_FT")
        os.system("cp "+WORK_DIR + tc_directory + "MDLforML/"+mdlfile_ac_2+" "+WORK_DIR + tc_directory + "sims/outputs_ac_2_FT/"+mdlfile_ac_2)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+parasiticfile+" "+WORK_DIR + tc_directory + "sims/outputs_ac_2_FT/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_2_FT/"+netlistfile)
        modify_spice_file_for_ac_2_sim(WORK_DIR, design, tbfile)
    else:
        logging.info("Ignoring ac2. Either mdl file does not exist or, simulation is not needed.")
    #
    if int(simcode[2])==1 and os.path.exists(WORK_DIR + tc_directory + "MDLforML/"+mdlfile_ac_3):
        is_in_measurement = False
        simulation_list.append(simulation("ac_3"))

        with open (WORK_DIR + tc_directory +"MDLforML/"+mdlfile_ac_3,"r") as fmdl:
            for line in fmdl:
                line = line.lstrip()
                if is_in_measurement == False:
                    if line.startswith("alias"):
                        is_in_measurement = True
                    elif line.startswith("foreach"):
                        pass
                    else:
                        pass
                else:
                    # if line.startswith("export"):
                        # spec_list_ac_3.append(specs(line.split()[2],spec_csv[line.split()[2]][0],spec_csv[line.split()[2]][1],spec_csv[line.split()[2]][2]))
                    if line.rstrip().endswith("}"):
                        is_in_measurement = False

        if not os.path.exists(WORK_DIR + tc_directory + "sims/outputs_ac_3_FT"):
            os.mkdir(WORK_DIR + tc_directory + "sims/outputs_ac_3_FT")
        os.system("cp "+WORK_DIR + tc_directory + "MDLforML/"+mdlfile_ac_3+" "+WORK_DIR + tc_directory +"sims/outputs_ac_3_FT/"+mdlfile_ac_3)
        os.system("cp "+WORK_DIR + tc_directory + "reworked_netlist/"+parasiticfile+" "+WORK_DIR + tc_directory +"sims/outputs_ac_3_FT/"+parasiticfile)
        os.system("cp "+WORK_DIR + tc_directory +"reworked_netlist/"+netlistfile+" "+ WORK_DIR + tc_directory +"sims/outputs_ac_3_FT/"+netlistfile)
        modify_spice_file_for_ac_3_sim(WORK_DIR, design, tbfile)
    else:
        logging.info("Ignoring ac3. Either mdl file does not exist or, simulation is not needed.")
    # return spec_list_ac_1,spec_list_ac_2,spec_list_ac_3,spec_list_dc_1,spec_list_tran_1,simulation_list
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
def modify_spice_file_for_tran_sim(WORK_DIR, design, infile_final):
    temp = ""
    tc_directory = "/" + design + "/"
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_tran_1_FT/"+infile_final,'w') as fout:
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
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_ac_2_FT/"+infile_final,'w') as fout:
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
    with open(WORK_DIR + tc_directory + "reworked_netlist/"+infile_final,'r') as fin, open(WORK_DIR + tc_directory + "sims/outputs_ac_3_FT/"+infile_final,'w') as fout:
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
