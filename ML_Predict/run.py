import logging
import argparse
import timeit
import os
import pdb
import pandas as pd

from parsefile.parsefile import extract_spice_netlist, read_nets_under_test,\
                                add_parasitics, extract_mdl,\
                                add_parasitics_for_FN, gen_constraints
from utils.utils import clean, create_critical_range_csv, merge_critical_range,\
                        set_wire_length_bounds_for_smartforce, create_csv_for_FT
from sims.sims import gen_outputs_ac_1, get_range_ac_1,\
                      gen_outputs_ac_2, get_range_ac_2,\
                      gen_outputs_ac_3, get_range_ac_3,\
                      gen_outputs_dc_1, get_range_dc_1,\
                      gen_outputs_tran_1, get_range_tran_1,\
                      generate_outputs_with_paramset_ac_1,\
                      generate_outputs_with_paramset_ac_2,\
                      generate_outputs_with_paramset_ac_3,\
                      generate_outputs_with_paramset_dc_1,\
                      generate_outputs_with_paramset_tran_1
from parsefile.parsefile_FT import extract_mdl_FT
from classifiers.analyses import analyses, analysis_with_svm, analysis_with_mlp

WORK_DIR = os.getcwd()
SAMPLE_COUNT_SPARSE = 1000
SAMPLE_COUNT_DENSE = 3000

parser = argparse.ArgumentParser(description = 'This functions generates ML \
                                 models from performance constraints.')
parser.add_argument('-design', '--design', type = str, metavar = '',
                    required = True, help = 'Netlist under test')
parser.add_argument('-sim', '--sim', type = str, metavar = '', required = False,
                    help = 'Required simulations. write a string consisting 1 \
                    and 0 to indicate which testbenches to consider with the \
                    following sequence: ac1ac2ac3dc1tran1 (e.g., 11001)')
# "-sim" is still not applied in the ECG flow.

args = parser.parse_args()
logging.basicConfig(filename = 'run.log', filemode = 'w', level = logging.INFO,
                    format = '%(name)s - %(levelname)s - %(message)s')


def parse_inputs(WORK_DIR, design, simcode):
    logging.info("Parsing input files...")
    nets_under_test = read_nets_under_test(WORK_DIR, design)
    logging.info("Nets under test: {}" .format(nets_under_test))
    subcircuit_list = extract_spice_netlist(WORK_DIR, design)
    param_list, param_name_list = add_parasitics(WORK_DIR, design, subcircuit_list)
    rewrite_testbench(WORK_DIR, design)
    logging.info("Added parameters: {}" .format(param_name_list))
    spec_list_ac_1,\
    spec_list_ac_2,\
    spec_list_ac_3,\
    spec_list_dc_1,\
    spec_list_tran_1,\
    simulation_list = extract_mdl(WORK_DIR, design, simcode)
    logging.info("Simulation Details: \n")
    for item in simulation_list:
        logging.info(item)
    create_critical_range_csv(WORK_DIR, design, param_name_list)
    return nets_under_test,\
           subcircuit_list, \
           spec_list_ac_1, \
           spec_list_ac_2, \
           spec_list_ac_3, \
           spec_list_dc_1, \
           spec_list_tran_1, \
           simulation_list, \
           param_list, \
           param_name_list

# """ This function reduces the feature space"""
def feature_space_pruning(WORK_DIR,
                          simulation_list,
                          spec_list_ac_1,
                          spec_list_ac_2,
                          spec_list_ac_3,
                          spec_list_dc_1,
                          spec_list_tran_1,
                          param_list,
                          param_name_list,
                          simcode):
    param_with_no_sens = param_name_list
    print("simcode: {}" .format(simcode))
    tc_directory = "/" + args.design + "/"
    if (int(simcode[0]) or int(simcode[1]) or int(simcode[2])):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+ args.design +".mdl"):
            gen_outputs_ac_1(WORK_DIR,
                             args.design,
                             simulation_list,
                             spec_list_ac_1,
                             param_name_list)
            param_with_no_sense_ac1 = get_range_ac_1(WORK_DIR,
                                                     args.design,
                                                     simulation_list,
                                                     param_list,
                                                     spec_list_ac_1)
        if (int(simcode[0])):
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_ac1))
#         # print(param_with_no_sense_ac1)
#         # print(param_with_no_sens)
    if int(simcode[1]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+ args.design +"_ac_2.mdl"):
            gen_outputs_ac_2(WORK_DIR,
                             args.design,
                             simulation_list,
                             spec_list_ac_2,
                             param_name_list)
            param_with_no_sense_ac2 = get_range_ac_2(WORK_DIR,
                                                     args.design,
                                                     simulation_list,
                                                     param_list,
                                                     spec_list_ac_2)
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_ac2))
#         # print(param_with_no_sense_ac2)
#         # print(param_with_no_sens)
    if int(simcode[2]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+ args.design +"_ac_3.mdl"):
            gen_outputs_ac_3(WORK_DIR,
                             args.design,
                             simulation_list,
                             spec_list_ac_3,
                             param_name_list)
            param_with_no_sense_ac3 = get_range_ac_3(WORK_DIR,
                                                     args.design,
                                                     simulation_list,
                                                     param_list,
                                                     spec_list_ac_3)
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_ac3))
#         # print(param_with_no_sense_ac3)
#         # print(param_with_no_sens)
    if int(simcode[3]): # For DC analysis
        if os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/"+ args.design +"_dc_1.mdl"):
            param_with_no_sense_dc1 = gen_outputs_dc_1(WORK_DIR,
                                                       args.design,
                                                       simulation_list,
                                                       spec_list_dc_1,
                                                       param_name_list)
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_dc1))
#
    if int(simcode[4]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforFSP/" + args.design +"_tran_1.mdl"):
            gen_outputs_tran_1(WORK_DIR,
                               args.design,
                               simulation_list,
                               spec_list_tran_1,
                               param_name_list)
            param_with_no_sense_tran1 = get_range_tran_1(WORK_DIR,
                                                         args.design,
                                                         simulation_list,
                                                         param_list,
                                                         spec_list_tran_1)
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_tran1))
#         # print(param_with_no_sense_tran1)
#         # print(param_with_no_sens)
#
    # print(param_with_no_sens)
    param_with_no_sens = list() # Forced to empty list for now
    merge_critical_range(WORK_DIR, args.design)
    set_wire_length_bounds_for_smartforce(WORK_DIR, args.design, param_with_no_sens)

"""Create netlist with adding LHS in the netlist"""
def configure_netlist_for_FT(WORK_DIR, design, subcircuit_list, simcode, TOTAL_SAMPLES):
    add_parasitics_for_FN(WORK_DIR, design, subcircuit_list, TOTAL_SAMPLES)
    extract_mdl_FT(WORK_DIR, simcode, design)

def rewrite_testbench(WORK_DIR, design):
    logging.info("Rewriting testbench...")
    tc_directory = "/" + design + "/"
    testbenchfile = design + "_tb.sp"
    testbenchfile_new = design + "_tb_new.sp"
    testbenchfile_new_for_ML = design + "_tb_new_for_ML.sp"
    modified_tb = ""
    modified_tb_for_ML = ""
    with open(WORK_DIR + tc_directory + testbenchfile, "r") as ftb:
        for line in ftb:
            line = line.strip()
            if line.startswith("include") or line.startswith(".include"):
                filename = line.split()[1].strip('\"').split("/")[-1]
                if filename == design + ".sp":
                    modified_tb = modified_tb + "include \"./" + design + "_with_parasitics.sp\"\n"
                    modified_tb_for_ML = modified_tb_for_ML + "include \"./" + design + "_with_parasitics_for_ML.sp\"\n"
                else:
                    modified_tb = modified_tb + line + "\n"
                    modified_tb_for_ML = modified_tb_for_ML + line + "\n"
            else:
                modified_tb = modified_tb + line + "\n"
                modified_tb_for_ML = modified_tb_for_ML + line + "\n"

    if not os.path.exists(WORK_DIR + tc_directory + "reworked_netlist"):
        os.mkdir(WORK_DIR + tc_directory + "reworked_netlist")

    with open(WORK_DIR + tc_directory + "reworked_netlist/" + testbenchfile_new, "w") as ftbnew:
        ftbnew.write(modified_tb)
    with open(WORK_DIR + tc_directory + "reworked_netlist/" + testbenchfile_new_for_ML, "w") as ftbnew:
        ftbnew.write(modified_tb_for_ML)

"""Simulate all required testbenches with the LHS"""
def simulations_for_FT(WORK_DIR, spec_list_ac_1,spec_list_ac_2, spec_list_ac_3,
                       spec_list_dc_1, spec_list_tran_1, simcode, mode):
    tc_directory = "/" + args.design + "/"
    if int(simcode[0]) or int(simcode[1]) or int(simcode[2]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + args.design +".mdl"):
            start_ac1 = timeit.default_timer()
            generate_outputs_with_paramset_ac_1(WORK_DIR,
                                                args.design,
                                                spec_list_ac_1,
                                                mode)
            stop_ac1 = timeit.default_timer()
            print("Time for ac1 simulation: {}" .format(stop_ac1 - start_ac1))
    if int(simcode[1]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + args.design +"_ac_2.mdl"):
            start_ac2 = timeit.default_timer()
            generate_outputs_with_paramset_ac_2(WORK_DIR,
                                                args.design,
                                                spec_list_ac_2,
                                                mode)
            stop_ac2 = timeit.default_timer()
            print("Time for ac2 simulation: {}" .format(stop_ac2 - start_ac2))
    if int(simcode[2]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + args.design +"_ac_3.mdl"):
            start_ac3 = timeit.default_timer()
            generate_outputs_with_paramset_ac_3(WORK_DIR,
                                                args.design,
                                                spec_list_ac_3,
                                                mode)
            stop_ac3 = timeit.default_timer()
            print("Time for ac3 simulation: {}" .format(stop_ac3 - start_ac3))
    if int(simcode[3]): # For DC1
        if os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + args.design +"_dc_1.mdl"):
            start_dc1 = timeit.default_timer()
            generate_outputs_with_paramset_dc_1(WORK_DIR,
                                                args.design,
                                                spec_list_dc_1,
                                                mode)
            stop_dc1 = timeit.default_timer()
            print("Time for dc1 simulation: {}" .format(stop_dc1 - start_dc1))
    if int(simcode[4]):
        if os.path.exists(WORK_DIR + tc_directory + "MDLforML/" + args.design +"_tran_1.mdl"):
            start_tran1 = timeit.default_timer()
            generate_outputs_with_paramset_tran_1(WORK_DIR,
                                                  args.design,
                                                  spec_list_tran_1,
                                                  mode)
            stop_tran1 = timeit.default_timer()
            print("Time for tran1 simulation: {}" .format(stop_tran1 - start_tran1))
    create_csv_for_FT(WORK_DIR, args.design, simcode, mode)

"""Set the list ps_of_interest"""
def set_ps_of_interest(WORK_DIR, design):
    tc_directory = "/" + design + "/"
    df_bounds = pd.read_csv(WORK_DIR
                            + tc_directory
                            + "outputs/node_under_test_for_smartforce.csv")
    df = pd.read_csv(WORK_DIR
                     + tc_directory
                     + 'outputs/database_for_FT_0.csv')
    df_specs = pd.read_csv(WORK_DIR
                           + tc_directory
                           + "spec_limits.csv").set_index('bounds')
    param_list = df_bounds.columns.tolist()
    headers_in_df = df.columns.tolist()
    #Use the following if alll specs are needed to be consdered
    ps_of_interest = [item for item in headers_in_df if item not in param_list]
    print("ps_of_interest: {}" .format(ps_of_interest))

    return ps_of_interest

def generate_constraints(WORK_DIR, design, param_list):
    tc_directory = "/" + design + "/"
    constraint = ""
    temp_pin_list = list()
    with open(WORK_DIR + tc_directory + "MLPredict.const", 'w') as fconst:
        for item in param_list:
            temp_list = item.name.split('_')
            temp_pin_list.append(temp_list[1] + "/" + temp_list[2] + "/" + item.pin + "/" +  temp_list[0])
    constraint = " , ".join(temp_pin_list)
    return constraint


def main():
    start = timeit.default_timer()
    mode = 0
    flag = 0
    constraints_for_align = ""
    clean(WORK_DIR, args.design)
    nets_under_test,\
    subcircuit_list, \
    spec_list_ac_1, \
    spec_list_ac_2, \
    spec_list_ac_3, \
    spec_list_dc_1, \
    spec_list_tran_1, \
    simulation_list, \
    param_list, \
    param_name_list = parse_inputs(WORK_DIR, args.design, args.sim)
    param_list_to_constraints = generate_constraints(WORK_DIR, args.design, param_list)
    feature_space_pruning(WORK_DIR,
                          simulation_list,
                          spec_list_ac_1,
                          spec_list_ac_2,
                          spec_list_ac_3,
                          spec_list_dc_1,
                          spec_list_tran_1,
                          param_list,
                          param_name_list,
                          args.sim)

    stop_feature_space_pruning = timeit.default_timer()
    configure_netlist_for_FT(WORK_DIR,
                             args.design,
                             subcircuit_list,
                             args.sim,
                             SAMPLE_COUNT_SPARSE)
    start_sim_with_sparse = timeit.default_timer()
    simulations_for_FT(WORK_DIR,
                       spec_list_ac_1,
                       spec_list_ac_2,
                       spec_list_ac_3,
                       spec_list_dc_1,
                       spec_list_tran_1,
                       args.sim,
                       mode)
    stop_sim_with_sparse = timeit.default_timer()
    ps_of_interest = set_ps_of_interest(WORK_DIR, args.design)
    flag = 0
    # # flag is used to indicate whether if a database with dense samples
    # # set is alread generated
    for item in ps_of_interest:
        constraints_for_align = constraints_for_align + "MLPredict ( " + str(item) + " , " + param_list_to_constraints + " )\n"
        print("item: {}" .format(item))
        accuracy = analysis_with_svm(WORK_DIR, args.design, param_name_list, item, 0)
        print("Classification accuracy: {}" .format(accuracy))
        if accuracy < 0.95:
            if accuracy >= 0.90:
                if flag == 0:
                    configure_netlist_for_FT(WORK_DIR,
                                             args.design,
                                             subcircuit_list,
                                             args.sim,
                                             SAMPLE_COUNT_DENSE)
                    start_sim_with_dense = timeit.default_timer()
                    simulations_for_FT(WORK_DIR,
                                       spec_list_ac_1,
                                       spec_list_ac_2,
                                       spec_list_ac_3,
                                       spec_list_dc_1,
                                       spec_list_tran_1,
                                       args.sim,
                                       1)
                    stop_sim_with_dense = timeit.default_timer()
                    flag = 1
                    accuracy = analysis_with_svm(WORK_DIR,
                                                 args.design,
                                                 param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
                else:
                    accuracy = analysis_with_svm(WORK_DIR,
                                                 args.design,
                                                 param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
            else:
                if flag == 0:
                    configure_netlist_for_FT(WORK_DIR,
                                             args.design,
                                             subcircuit_list,
                                             args.sim,
                                             SAMPLE_COUNT_DENSE)
                    start_sim_with_dense = timeit.default_timer()
                    simulations_for_FT(WORK_DIR,
                                       spec_list_ac_1,
                                       spec_list_ac_2,
                                       spec_list_ac_3,
                                       spec_list_dc_1,
                                       spec_list_tran_1,
                                       args.sim,
                                       1)
                    stop_sim_with_dense = timeit.default_timer()
                    flag = 1
                    accuracy = analysis_with_mlp(WORK_DIR,
                                                 args.design,
                                                 param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
                else:
                    accuracy = analysis_with_mlp(WORK_DIR,
                                                 args.design,
                                                 param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
    with open(WORK_DIR + "/" + args.design + "/outputs/MLPredict.const", 'w') as fconst:
        fconst.write(constraints_for_align)
if __name__ == "__main__":
    main()
