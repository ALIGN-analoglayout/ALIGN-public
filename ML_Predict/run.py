
import logging
import argparse
import timeit
import os
import pandas as pd

from utils.utils import clean, create_critical_range_csv, merge_critical_range,\
                        set_wire_length_bounds_for_smartforce, create_csv_for_FT
from parsefile.parsefile import extract_netlist, read_nodes_under_test,\
                                add_parasitics_for_FSP, extract_mdl,\
                                add_parasitics_for_FN, gen_constraints
from parsefile.parsefile_FT import extract_mdl_FT
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
from classifiers.analyses import analyses, analysis_with_svm, analysis_with_mlp

# Add the device type, primitive cell types used in the netlist in
# the following set
device_type_set = {
    'resistor', 'capacitor', 'nmos_rf',
    'pch', 'vsource', 'isource',
    'vcvs', 'nfet', 'pfet',
    'rmres', 'nfet_b', 'pfet_b',
    }

# Constants
SAMPLE_COUNT_SPARSE = 1000
SAMPLE_COUNT_DENSE = 2000

parser = argparse.ArgumentParser(description = 'This functions generates ML \
                                 models from performance constraints.')
parser.add_argument('-design', '--design', type = str, metavar = '',
                    required = True, help = 'Netlist under test')
parser.add_argument('-type', '--parasitic', type = str, metavar = '',
                    required = False, help = 'Parasitic type')
parser.add_argument('-spec', '--spec', type = str, metavar = '',
                    required = False, help = 'Spec for sensitivity analysis')
parser.add_argument('-sim', '--sim', type = str, metavar = '', required = False,
                    help = 'Required simulations. write a string consisting 1 \
                    and 0 to indicate which testbenches to consider with the \
                    following sequence: ac1ac2ac3dc1tran1 (e.g., 11001)')
# "-sim" is still not applied in the ECG flow.

args = parser.parse_args()
logging.basicConfig(filename = 'test.log', level = logging.INFO,
                    format = '%(levelname)s:%(message)s')

def parse_inputs(WORK_DIR):
    nodes_under_test = read_nodes_under_test(WORK_DIR)
    device_list, node_list = extract_netlist(WORK_DIR,
                                             args.design, nodes_under_test,
                                             device_type_set)
    param_list, param_name_list = add_parasitics_for_FSP(WORK_DIR,
                                                         args.design,
                                                         device_list, node_list)
    spec_list_ac_1,\
    spec_list_ac_2,\
    spec_list_ac_3,\
    spec_list_dc_1,\
    spec_list_tran_1,\
    simulation_list = extract_mdl(WORK_DIR, args.design)
    create_critical_range_csv(WORK_DIR,
                              param_name_list)
    return nodes_under_test,\
           device_list, \
           node_list, \
           spec_list_ac_1, \
           spec_list_ac_2, \
           spec_list_ac_3, \
           spec_list_dc_1, \
           spec_list_tran_1, \
           simulation_list, \
           param_list, \
           param_name_list
""" This function reduces the feature space"""
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
    if (int(simcode[0]) or int(simcode[1]) or int(simcode[2])):
        gen_outputs_ac_1(WORK_DIR,
                         args.design,
                         simulation_list,
                         spec_list_ac_1,
                         param_name_list)
        param_with_no_sense_ac1 = get_range_ac_1(WORK_DIR,
                                                 simulation_list,
                                                 param_list,
                                                 spec_list_ac_1)
        if (int(simcode[0])):
            param_with_no_sens = list(set(param_with_no_sens) \
                                      & set(param_with_no_sense_ac1))
        # print(param_with_no_sense_ac1)
        # print(param_with_no_sens)
    if int(simcode[1]):
        gen_outputs_ac_2(WORK_DIR,
                         args.design,
                         simulation_list,
                         spec_list_ac_2,
                         param_name_list)
        param_with_no_sense_ac2 = get_range_ac_2(WORK_DIR,
                                                 simulation_list,
                                                 param_list,
                                                 spec_list_ac_2)
        param_with_no_sens = list(set(param_with_no_sens) \
                                  & set(param_with_no_sense_ac2))
        # print(param_with_no_sense_ac2)
        # print(param_with_no_sens)
    if int(simcode[2]):
        gen_outputs_ac_3(WORK_DIR,
                         args.design,
                         simulation_list,
                         spec_list_ac_3,
                         param_name_list)
        param_with_no_sense_ac3 = get_range_ac_3(WORK_DIR,
                                                 simulation_list,
                                                 param_list,
                                                 spec_list_ac_3)
        param_with_no_sens = list(set(param_with_no_sens) \
                                  & set(param_with_no_sense_ac3))
        # print(param_with_no_sense_ac3)
        # print(param_with_no_sens)
    if int(simcode[3]): # For DC analysis
        param_with_no_sense_dc1 = gen_outputs_dc_1(WORK_DIR,
                                                   args.design,
                                                   simulation_list,
                                                   spec_list_dc_1,
                                                   param_name_list)
        param_with_no_sens = list(set(param_with_no_sens) \
                                  & set(param_with_no_sense_dc1))

    if int(simcode[4]):
        gen_outputs_tran_1(WORK_DIR,
                           args.design,
                           simulation_list,
                           spec_list_tran_1,
                           param_name_list)
        param_with_no_sense_tran1 = get_range_tran_1(WORK_DIR,
                                                     simulation_list,
                                                     param_list,
                                                     spec_list_tran_1)
        param_with_no_sens = list(set(param_with_no_sens) \
                                  & set(param_with_no_sense_tran1))
        # print(param_with_no_sense_tran1)
        # print(param_with_no_sens)

    print(param_with_no_sens)
    merge_critical_range(WORK_DIR)
    set_wire_length_bounds_for_smartforce(WORK_DIR, param_with_no_sens)

"""Create netlist with adding LHS in the netlist"""
def configure_netlist_for_FT(WORK_DIR, device_list, node_list, TOTAL_SAMPLES):
    add_parasitics_for_FN(WORK_DIR, args.design, device_list, node_list,
                          TOTAL_SAMPLES)
    extract_mdl_FT(WORK_DIR, args.design)

"""Simulate all required testbenches with the LHS"""
def simulations_for_FT(WORK_DIR, spec_list_ac_1,spec_list_ac_2, spec_list_ac_3,
                       spec_list_dc_1, spec_list_tran_1, simcode, mode):
    if int(simcode[0]) or int(simcode[1]) or int(simcode[2]):
        start_ac1 = timeit.default_timer()
        generate_outputs_with_paramset_ac_1(WORK_DIR,
                                            args.design,
                                            spec_list_ac_1,
                                            mode)
        stop_ac1 = timeit.default_timer()
        print("Time for ac1 simulation: {}" .format(stop_ac1 - start_ac1))
    if int(simcode[1]):
        start_ac2 = timeit.default_timer()
        generate_outputs_with_paramset_ac_2(WORK_DIR,
                                            args.design,
                                            spec_list_ac_2,
                                            mode)
        stop_ac2 = timeit.default_timer()
        print("Time for ac2 simulation: {}" .format(stop_ac2 - start_ac2))
    if int(simcode[2]):
        start_ac3 = timeit.default_timer()
        generate_outputs_with_paramset_ac_3(WORK_DIR,
                                            args.design,
                                            spec_list_ac_3,
                                            mode)
        stop_ac3 = timeit.default_timer()
        print("Time for ac3 simulation: {}" .format(stop_ac3 - start_ac3))
    if int(simcode[3]): # For DC1
        start_dc1 = timeit.default_timer()
        generate_outputs_with_paramset_dc_1(WORK_DIR,
                                            args.design,
                                            spec_list_dc_1,
                                            mode)
        stop_dc1 = timeit.default_timer()
        print("Time for dc1 simulation: {}" .format(stop_dc1 - start_dc1))
    if int(simcode[4]):
        start_tran1 = timeit.default_timer()
        generate_outputs_with_paramset_tran_1(WORK_DIR,
                                              args.design,
                                              spec_list_tran_1,
                                              mode)
        stop_tran1 = timeit.default_timer()
        print("Time for tran1 simulation: {}" .format(stop_tran1 - start_tran1))
    create_csv_for_FT(WORK_DIR, simcode, mode)

"""Set the list ps_of_interest"""
def set_ps_of_interest(WORK_DIR):
    df_bounds = pd.read_csv(WORK_DIR
                            + "/outputs/node_under_test_for_smartforce.csv")
    df = pd.read_csv(WORK_DIR
                     + '/outputs/database_for_FT_0.csv')
    df_specs = pd.read_csv(WORK_DIR
                           + "/inputs/spec_limits.csv").set_index('bounds')
    param_list = df_bounds.columns.tolist()
    headers_in_df = df.columns.tolist()
    #Use the following if alll specs are needed to be consdered
    ps_of_interest = [item for item in headers_in_df if item not in param_list]
    print("ps_of_interest: {}" .format(ps_of_interest))

    return ps_of_interest

def prepare_constraints_for_ALIGN(WORK_DIR, param_name_list, ps_of_interest):
    with open(WORK_DIR+"/outputs/"+args.design+".const","w") as fconst:
        fconst.write("MLPredict ( "+ps_of_interest+" ,")
        for i, item in enumerate(param_name_list):
            temp_param = " "
            temp_splited_string = item.split("_")
            temp_param = temp_param + temp_splited_string[1] + "/" + temp_splited_string[2]
            print(temp_splited_string[0])
            if temp_splited_string[0] == "rp":
                temp_param = temp_param + "/r"
            else:
                temp_param = temp_param + "/c"
            if i == (len(param_name_list)-1):
                temp_param = temp_param + " )"
            else:
                temp_param = temp_param + " ,"
            fconst.write(temp_param)
    pass


def main():
    start = timeit.default_timer()
    # Other variables
    mode = 0
    flag = 0
    constraints_for_align = ""
    global SAMPLE_COUNT_SPARSE
    global SAMPLE_COUNT_DENSE
    WORK_DIR = os.getcwd()

    clean(WORK_DIR)

    nodes_under_test, \
    device_list, \
    node_list, \
    spec_list_ac_1, \
    spec_list_ac_2, \
    spec_list_ac_3, \
    spec_list_dc_1, \
    spec_list_tran_1, \
    simulation_list, \
    param_list, \
    param_name_list = parse_inputs(WORK_DIR)
    param_list_for_const_file = gen_constraints(WORK_DIR,
                                                args.design, param_name_list)
    start_feature_space_pruning = timeit.default_timer()
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
                             device_list,
                             node_list,
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
    ps_of_interest = set_ps_of_interest(WORK_DIR)
    flag = 0
    # flag is used to indicate whether if a database with dense samples
    # set is alread generated
    for item in ps_of_interest:
        print("item: {}" .format(item))
        accuracy = analysis_with_svm(WORK_DIR, param_name_list, item, 0)
        print("Classification accuracy: {}" .format(accuracy))
    #     breakpoint()
        if accuracy < 0.95:
            if accuracy >= 0.90:
                if flag == 0:
                    configure_netlist_for_FT(WORK_DIR, device_list, node_list,
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
                    accuracy = analysis_with_svm(WORK_DIR, param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
                else:
                    accuracy = analysis_with_svm(WORK_DIR, param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
            else:
                if flag == 0:
                    configure_netlist_for_FT(WORK_DIR, device_list, node_list,
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
                    accuracy = analysis_with_mlp(WORK_DIR, param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))
                else:
                    accuracy = analysis_with_mlp(WORK_DIR, param_name_list,
                                                 item, 1)
                    print("Acc: {}" .format(accuracy))

    # print("Time for feature space pruning: {}" \
    #        .format(stop_feature_space_pruning - start_feature_space_pruning))
    # print("Simulation time with sparse set: {}" \
    #        .format(stop_sim_with_sparse - start_sim_with_sparse))
    # print("Simulation time with dense set: {}" \
    #        .format(stop_sim_with_dense - start_sim_with_dense))


if __name__ == "__main__":
    main()
