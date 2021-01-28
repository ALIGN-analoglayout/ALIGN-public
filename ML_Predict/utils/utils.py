import os
import csv
import glob
import numpy as np
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
from pyDOE import *

def clean(WORK_DIR):
    print("Running clean()")
    os.chdir(WORK_DIR + "/sims/critical_range_all")
    os.system("rm -f *.csv")
    pass

def create_critical_range_csv(WORK_DIR,param_name_list):
    with open(WORK_DIR+"/outputs/critical_range_template.csv",'w') as fcrit:
        csv_writer = csv.writer(fcrit)
        temp = list()
        for item in param_name_list:
                temp.append(item)
        csv_writer.writerow(temp)
    pass

def merge_critical_range(WORK_DIR):
    print("Running merge_critical_range()")
    os.chdir(WORK_DIR + "/sims/critical_range_all")
    if os.path.exists("merged_critical_range.csv"):
        os.system("rm -f merged_critical_range.csv")
    all_files = glob.glob("critical_range_*.csv")
    # df_merged = pd.concat(df_from_each_file, ignore_index=True)
    df_merged = pd.concat((pd.read_csv(f, sep = ',') for f in all_files), ignore_index = True)
    df_merged.to_csv("merged_critical_range.csv", index = False)
    os.chdir(WORK_DIR)
    pass

def set_wire_length_bounds_for_smartforce(WORK_DIR, param_with_no_sens):
    print("Running set_wire_length_bounds_for_smartforce()")
    os.chdir(WORK_DIR + "/sims/critical_range_all")
    if os.path.exists(WORK_DIR + "/outputs/node_under_test_for_smartforce.csv"):
        os.system("rm -f "
                  + WORK_DIR
                  + "/outputs/node_under_test_for_smartforce.csv")
    df = pd.read_csv("merged_critical_range.csv")
    df_new = pd.DataFrame(columns = df.columns, index = ['value', 'PW'])
    print(df_new)
    for item in df.columns:
        if item not in param_with_no_sens:
            df_new.loc[['value'],[item]] = min(df[item])
            df_new.loc[['PW'],[item]] = 1
        else:
            df_new = df_new.drop(columns = [item])
    # for item in df.columns:
    #     if (df_new.loc[['value'],[item]] == 20).bool():
    #         # print(item)
    #         df_new = df_new.drop(columns=[item])
    print(df_new)
    df_new.to_csv(WORK_DIR
                  + "/outputs/node_under_test_for_smartforce.csv", index = False)

def get_lhs_samples(WORK_DIR, TOTAL_SAMPLES):
    os.chdir(WORK_DIR+"/utils/")
    np.set_printoptions(suppress=True)
    temp = ""
    temp2 = ""
    min_val = 1
    fdata = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    lhs_data = np.matrix(lhs(len(fdata.columns), samples = TOTAL_SAMPLES, criterion='center')).transpose()
    row_id = 0
    rows_to_merge = 0
    for item in fdata.columns:
        # print(lhs_data[row_id])
        lhs_data[row_id] = lhs_data[row_id] * float(fdata[item][0]) + float(min_val)
        row_id = row_id + 1
    lhs_data = lhs_data.transpose()
    # breakpoint()
    # print(lhs_data)
    with open("paramset.txt",'w') as f:
        f.write(' '.join(fdata.columns) + '\n')
        temp = temp + "data paramset {\n\t" + ' '.join(fdata.columns) + '\n'
        for row in lhs_data:
            # print(row)
            f.write(str(np.round(row,5)).strip('[').strip(']').strip('\n') + '\n')
            temp = temp + '\t' + str(np.round(row,5)).strip('[').strip(']') + '\n'
        temp = temp + "\t}\n"
        rows_to_merge = len(str(np.round(row,5)).strip('[').strip(']').split('\n'))
        # print("Column counts in matrix: {}".format(rows_to_merge))
        # breakpoint()
    with open("paramset.txt",'r') as f:
        for count,line in enumerate(f):
            if not count%rows_to_merge== 0:
                temp2 = temp2 + line.strip('\n') + ' '
            else:
                temp2 = temp2 + line
        # print(temp2)
    with open("paramset.txt",'w') as f:
        f.write(temp2)

    os.chdir(WORK_DIR)
    return "data paramset {\n\t"+temp2+"\t}\n"
    # return temp
    # print(temp)
    pass

def create_csv_for_FT(WORK_DIR, simcode, MODE):
    """
    Creates a combined database with all performance specification of all samples.
    """
    os.chdir(WORK_DIR + "/outputs/")
    # logging.info("Function: create_csv() is under processing...")
    # if not os.path.exists("optimize_bounds"):
    #     os.mkdir("optimize_bounds")
    with open("database_for_FT_" + str(MODE) + ".csv", 'w') as fdb, \
             open(WORK_DIR + "/utils/paramset.txt", 'r') as fmeas:
        if int(simcode[0]):
            fgain = open(WORK_DIR
                         + "/sims/outputs_ac_1_FT/maxgain_"
                         + str(MODE), 'r')
            fugf = open(WORK_DIR
                        + "/sims/outputs_ac_1_FT/gainbwprod_"
                        + str(MODE), 'r')
            fpm = open(WORK_DIR
                       + "/sims/outputs_ac_1_FT/pm_"
                       + str(MODE), 'r')
            fbwout = open(WORK_DIR
                          + "/sims/outputs_ac_1_FT/bwout_"
                          + str(MODE), 'r')
        if int(simcode[1]):
            fCMRR = open(WORK_DIR
                         + "/sims/outputs_ac_2_FT/CMRR_"
                         + str(MODE), 'r')
        if int(simcode[2]):
            fPSRR = open(WORK_DIR
                         + "/sims/outputs_ac_3_FT/PSRR_"
                         + str(MODE), 'r')
        if int(simcode[3]):
            fICMR = open(WORK_DIR
                         + "/sims/outputs_dc_1_FT/ICMR_"
                         + str(MODE), 'r')
            pass
        if int(simcode[4]):
            fSR = open(WORK_DIR
                       + "/sims/outputs_tran_1_FT/SR_"
                       + str(MODE), 'r')
        csv_writer = csv.writer(fdb)
        for line in fmeas:
            temp = line.split()
            if int(simcode[0]):
                temp = temp + fgain.readline().split()
                temp = temp + fbwout.readline().split()
                temp = temp + fugf.readline().split()
                temp = temp + fpm.readline().split()
            if int(simcode[1]):
                temp = temp + fCMRR.readline().split()
            if int(simcode[2]):
                temp = temp + fPSRR.readline().split()
            if int(simcode[3]):
                temp = temp + fICMR.readline().split()
                pass
            if int(simcode[4]):
                temp = temp + fSR.readline().split()

            csv_writer.writerow(temp)
            # print(temp)
    # logging.info("Function: create_csv() is processed successfully.")
    pass

def scatterplot_2D(X,Y,Result,Xname,Yname):
    ax = sns.scatterplot(x=X,y=Y, hue=Result, palette=[sns.xkcd_rgb["pale red"],sns.xkcd_rgb["denim blue"]], edgecolor='black', legend=False)
    plt.xlabel(Xname)
    plt.ylabel(Yname)
    # plt.title(item)
    # plt.xlim(0,1.1)
    # plt.legend(loc='lower left', handles=['0','1'],labels=['Doesss','Does'])
    # plot_svc_decision_function(model=svcclassifier,plot_support=True)
    plt.show()
