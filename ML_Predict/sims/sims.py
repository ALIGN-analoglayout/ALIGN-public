import os
import csv
import numpy as np
import pandas as pd

def gen_outputs_ac_1(WORK_DIR,design,simulation_list,spec_list_ac_1,param_name_list):
    infile_final = design + "_final.sp"
    spicelogfile = design + ".log"
    mdlfile = design + ".mdl"
    measurefile_ac_1 = design + ".measure"

    os.chdir(WORK_DIR+"/sims/outputs_ac_1")
    print("Current Simulation: ac_1")
    filenames = list()
    temp_spec_list = list()
    for num, item in enumerate(simulation_list):
        if item.name == "ac_1":
            sim_id = num
            break
    # print(sim_id)
    sim_count = int(simulation_list[sim_id].count[sim_id])
    for item in spec_list_ac_1:
        temp_spec_list.append(item.name)

    for item in param_name_list:
        # if node.isundertest == True:
        #     # for dev in node.devlist:
            # if node.alias != None:
            #     param_to_vary = "lp_"+node.alias
            # else :
            #     param_to_vary = "lp_"+node.name
            param_to_vary = item
            # param_name_list.append(param_to_vary)
            print("Variable under simulation: {}".format(param_to_vary))
            modify_mdl(param_to_vary,"ac_1",design)
            os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile+" > "+spicelogfile)
            # breakpoint()
            fdata = open(param_to_vary+".csv", 'w')
            fdata_writer = csv.writer(fdata)
            fdata_writer.writerow(temp_spec_list)

            with open(measurefile_ac_1,'r') as fmeas:
                # print("row = {}, col = {}".format(len(spec_list_ac_1),scount))
                temp = ""
                temp_matrix = np.zeros((1,len(spec_list_ac_1)*sim_count))
                for lineindex,line in enumerate(fmeas):
                    if lineindex > 10:
                        if not line.startswith('\n'):
                            # print(line)
                            if not (line.split('=')[1].strip()=="NaN"):
                                temp = temp + line.split('=')[1] + " "
                            else:
                                temp = temp + str(-2e99) + " "
                            # temp.append(line.split('=')[1])
                A = np.matrix(temp).reshape(len(spec_list_ac_1),sim_count).transpose()

                for i in range(sim_count):
                    fdata_writer.writerow(np.array(A[i]).flat)
    os.chdir(WORK_DIR)
    pass

def get_range_ac_1(WORK_DIR,simulation_list,param_list,spec_list_ac_1):
    os.chdir(WORK_DIR+"/sims/outputs_ac_1")
    print("Running get_range_ac_1")
    param_with_zero_sense = list()
    for num, item in enumerate(simulation_list):
        if item.name == "ac_1":
            sim_id = num
            break
    # print("Start: {}. Stop: {}, Step: {}".format(simulation_list[-3].start[0],simulation_list[-3].stop[0],simulation_list[-3].step[0]))
    step = float(simulation_list[sim_id].step[sim_id])
    stop = float(simulation_list[sim_id].stop[sim_id])
    fdb = pd.read_csv(WORK_DIR+"/outputs/critical_range_template.csv")
    temp_dict = {key: list() for key in fdb.columns}
    for p in param_list:
        # print("param under test: {}".format(p.name))
        df = pd.read_csv(p.name+".csv")
        min_critval = 1e99
        # print("parameter: {}" .format(p.name))
        # print("df1: {}" .format(df.loc[1,:].values))
        # print("df0: {}" .format(df.loc[0,:].values))
        # print(df.loc[1,:].values - df.loc[0,:].values)
        if (df.loc[1,:].values - df.loc[0,:].values).sum() == 0:
            param_with_zero_sense.append(p.name)
            print(p.name)
        for item in spec_list_ac_1:
            # print("item under test: {}".format(item.name))
            flag = 0
            min_critval = 1e99
            for i in range(len(df[item.name])):
                if (df[item.name][i] < float(item.minval)) or (df[item.name][i] > float(item.maxval)):
                    flag = 1
                    # If this loop as active at i=0, min_critval will be negative. However, the system should work at i=0.
                    if min_critval > (i-1)*float(simulation_list[sim_id].step[0]):
                        min_critval = (i-1)*float(simulation_list[sim_id].step[0])
                    break
            if flag == 0:
                if min_critval > float(simulation_list[sim_id].stop[0]):
                    min_critval = float(simulation_list[sim_id].stop[0])
            p.critval = min_critval
            temp_dict[p.name].append(p.critval)
    df1=pd.DataFrame.from_dict(temp_dict,orient='index').transpose()
    fdb = fdb.append(df1,sort=True,ignore_index=True)
    # # print(df.head(6))
    fdb.to_csv("critical_range_ac_1.csv",index=False)
    if not os.path.exists("../critical_range_all"):
        os.mkdir("../critical_range_all")
    os.system("cp "+"critical_range_ac_1.csv"+" "+"../critical_range_all/critical_range_ac_1.csv")
    os.chdir(WORK_DIR)
    return param_with_zero_sense
    pass


def gen_outputs_ac_2(WORK_DIR,design,simulation_list,spec_list_ac_2,param_name_list):
    os.chdir(WORK_DIR+"/sims/outputs_ac_2")
    infile_final = design + "_final.sp"
    spicelogfile = design + ".log"
    mdlfile_ac_2 = design + "_ac_2.mdl"
    measurefile_ac_2 = design + "_ac_2.measure"
    print("Current Simulation: ac_2")
    filenames = list()
    temp_spec_list = list()
    for num, item in enumerate(simulation_list):
        if item.name == "ac_2":
            sim_id = num
            break
    sim_count = int(simulation_list[sim_id].count[0])
    for item in spec_list_ac_2:
        temp_spec_list.append(item.name)

    for item in param_name_list:
        # if node.isundertest == True:
        #     # for dev in node.devlist:
            # if node.alias != None:
            #     param_to_vary = "lp_"+node.alias
            # else :
            #     param_to_vary = "lp_"+node.name
            param_to_vary = item
            print("Variable under simulation: {}".format(param_to_vary))
            modify_mdl(param_to_vary,"ac_2",design)
            os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_ac_2+" > "+spicelogfile)
            # breakpoint()
            fdata = open(param_to_vary+".csv", 'w')
            fdata_writer = csv.writer(fdata)
            fdata_writer.writerow(temp_spec_list)

            with open(measurefile_ac_2,'r') as fmeas:
                # print("row = {}, col = {}".format(len(spec_list_ac_1),scount))
                temp = ""
                temp_matrix = np.zeros((1,len(spec_list_ac_2)*sim_count))
                for lineindex,line in enumerate(fmeas):
                    if lineindex > 10:
                        if not line.startswith('\n'):
                            # print(line)
                            if not (line.split('=')[1].strip()=="NaN"):
                                temp = temp + line.split('=')[1] + " "
                            else:
                                temp = temp + str(-2e99) + " "
                            # temp.append(line.split('=')[1])
                A = np.matrix(temp).reshape(len(spec_list_ac_2),sim_count).transpose()

                for i in range(sim_count):
                    fdata_writer.writerow(np.array(A[i]).flat)
    os.chdir(WORK_DIR)
    pass

def get_range_ac_2(WORK_DIR,simulation_list,param_list,spec_list_ac_2):
    param_with_zero_sense = list()
    os.chdir(WORK_DIR+"/sims/outputs_ac_2")
    print("Running get_range_ac_2")
    for num, item in enumerate(simulation_list):
        if item.name == "ac_2":
            sim_id = num
            break
    # print("Simulation type: {}".format(simulation_list[sim_id].name))
    # print("Start: {}. Stop: {}, Step: {}".format(simulation_list[-3].start[0],simulation_list[-3].stop[0],simulation_list[-3].step[0]))
    step = float(simulation_list[sim_id].step[0])
    stop = float(simulation_list[sim_id].stop[0])
    fdb = pd.read_csv(WORK_DIR+"/outputs/critical_range_template.csv")
    temp_dict = {key: list() for key in fdb.columns}
    for p in param_list:
        # print("param under test: {}".format(p.name))
        df = pd.read_csv(p.name+".csv")
        df_ac1 = pd.read_csv("../outputs_ac_1/"+p.name+".csv")
        df_CMRR = df_ac1['maxgain'] - df['CMGain']
        # print(df_CMRR)
        # print(len(df_CMRR))
        min_critval = 1e99
        if (df_CMRR.loc[1] - df_CMRR.loc[0]).sum() == 0:
            param_with_zero_sense.append(p.name)
            print(p.name)
        for item in spec_list_ac_2:
            # print("item under test: {}".format(item.name))
            flag = 0
            min_critval = 1e99
            for i in range(len(df_CMRR)):
                if (df_CMRR[i] < float(item.minval)) or (df_CMRR[i] > float(item.maxval)):
                    flag = 1
                    if min_critval > i*float(simulation_list[sim_id].step[0]):
                        min_critval = i*float(simulation_list[sim_id].step[0])
                    break
            if flag == 0:
                if min_critval > float(simulation_list[sim_id].stop[0]):
                    min_critval = float(simulation_list[sim_id].stop[0])
            p.critval = min_critval
            temp_dict[p.name].append(p.critval)
    df1=pd.DataFrame.from_dict(temp_dict,orient='index').transpose()
    fdb = fdb.append(df1,sort=True,ignore_index=True)
    # # print(df.head(6))
    fdb.to_csv("critical_range"+"_ac_2.csv",index=False)
    if not os.path.exists("../critical_range_all"):
        os.mkdir("../critical_range_all")
    os.system("cp critical_range_ac_2.csv ../critical_range_all/critical_range_ac_2.csv")
    os.chdir(WORK_DIR)
    return param_with_zero_sense
    pass

def gen_outputs_ac_3(WORK_DIR,design,simulation_list,spec_list_ac_3,param_name_list):
    os.chdir(WORK_DIR+"/sims/outputs_ac_3")
    infile_final = design + "_final.sp"
    spicelogfile = design + ".log"
    mdlfile_ac_3 = design + "_ac_3.mdl"
    measurefile_ac_3 = design + "_ac_3.measure"
    print("Current Simulation: ac_3")
    filenames = list()
    temp_spec_list = list()
    for num, item in enumerate(simulation_list):
        if item.name == "ac_3":
            sim_id = num
            break
    sim_count = int(simulation_list[sim_id].count[0])
    for item in spec_list_ac_3:
        temp_spec_list.append(item.name)

    for item in param_name_list:
        # if node.isundertest == True:
        #     # for dev in node.devlist:
            # if node.alias != None:
            #     param_to_vary = "lp_"+node.alias
            # else :
            #     param_to_vary = "lp_"+node.name
            param_to_vary = item
            print("Variable under simulation: {}".format(param_to_vary))
            modify_mdl(param_to_vary,"ac_3",design)
            os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_ac_3+" > "+spicelogfile)
            # breakpoint()
            fdata = open(param_to_vary+".csv", 'w')
            fdata_writer = csv.writer(fdata)
            fdata_writer.writerow(temp_spec_list)

            with open(measurefile_ac_3,'r') as fmeas:
                # print("row = {}, col = {}".format(len(spec_list_ac_1),scount))
                temp = ""
                temp_matrix = np.zeros((1,len(spec_list_ac_3)*sim_count))
                for lineindex,line in enumerate(fmeas):
                    if lineindex > 10:
                        if not line.startswith('\n'):
                            # print(line)
                            if not (line.split('=')[1].strip()=="NaN"):
                                temp = temp + line.split('=')[1] + " "
                            else:
                                temp = temp + str(-2e99) + " "
                            # temp.append(line.split('=')[1])
                A = np.matrix(temp).reshape(len(spec_list_ac_3),sim_count).transpose()

                for i in range(sim_count):
                    fdata_writer.writerow(np.array(A[i]).flat)

    os.chdir(WORK_DIR)
    pass

def get_range_ac_3(WORK_DIR,simulation_list,param_list,spec_list_ac_3):
    param_with_zero_sense = list()
    os.chdir(WORK_DIR+"/sims/outputs_ac_3")
    print("Running get_range_ac_3")
    for num, item in enumerate(simulation_list):
        if item.name == "ac_3":
            sim_id = num
            break
    # print("Simulation type: {}".format(simulation_list[sim_id].name))
    # print("Start: {}. Stop: {}, Step: {}".format(simulation_list[-3].start[0],simulation_list[-3].stop[0],simulation_list[-3].step[0]))
    step = float(simulation_list[sim_id].step[0])
    stop = float(simulation_list[sim_id].stop[0])
    fdb = pd.read_csv(WORK_DIR+"/outputs/critical_range_template.csv")
    temp_dict = {key: list() for key in fdb.columns}
    for p in param_list:
        # print("param under test: {}".format(p.name))
        df = pd.read_csv(p.name+".csv")
        df_ac1 = pd.read_csv("../outputs_ac_1/"+p.name+".csv")
        df_PSRR = df_ac1['maxgain'] - df['PSGain']
        # print(df_PSRR)
        # print(len(df_CMRR))
        min_critval = 1e99
        if (df_PSRR.loc[1] - df_PSRR.loc[0]).sum() == 0:
            param_with_zero_sense.append(p.name)
            print(p.name)
        for item in spec_list_ac_3:
            # print("item under test: {}".format(item.name))
            flag = 0
            min_critval = 1e99
            for i in range(len(df_PSRR)):
                if (df_PSRR[i] < float(item.minval)) or (df_PSRR[i] > float(item.maxval)):
                    flag = 1
                    if min_critval > i*float(simulation_list[sim_id].step[0]):
                        min_critval = i*float(simulation_list[sim_id].step[0])
                    break
            if flag == 0:
                if min_critval > float(simulation_list[sim_id].stop[0]):
                    min_critval = float(simulation_list[sim_id].stop[0])
            p.critval = min_critval
            temp_dict[p.name].append(p.critval)
    df1=pd.DataFrame.from_dict(temp_dict,orient='index').transpose()
    fdb = fdb.append(df1,sort=True,ignore_index=True)
    # # print(df.head(6))
    fdb.to_csv("critical_range_ac_3.csv",index=False)
    if not os.path.exists("../critical_range_all"):
        os.mkdir("../critical_range_all")
    os.system("cp "+"critical_range_ac_3.csv"+" "+"../critical_range_all/critical_range_ac_3.csv")
    os.chdir(WORK_DIR)
    return param_with_zero_sense
    pass

def gen_outputs_dc_1(WORK_DIR,
                     design,
                     simulation_list,
                     spec_list_dc_1,
                     param_name_list):
    os.chdir(WORK_DIR + "/sims/outputs_dc_1")
    infile_final = design + "_final.sp"
    spicelogfile_dc_1 = design + ".log"
    mdlfile_dc_1 = design + "_dc_1.mdl"
    measurefile_dc_1 = design + "_dc_1.measure"
    print("Current Simulation: dc_1")
    filenames = list()
    temp_spec_list = list()
    for num, item in enumerate(simulation_list):
        if item.name == "dc_1":
            sim_id = num
            break
    sim_count = int(simulation_list[sim_id].count[sim_id])
    for item in spec_list_dc_1:
        temp_spec_list.append(item)
    fdb = pd.read_csv(WORK_DIR + "/outputs/critical_range_template.csv")
    min_icmr = {key: simulation_list[sim_id].stop[0] for key in fdb.columns}
    for item in param_name_list:
        param_to_vary = item
        print("Variable under simulation: {}" .format(param_to_vary))
        modify_mdl(param_to_vary, "dc_1", design)
        os.system("spectremdl -design "
                  + infile_final
                  + " -batch "
                  + mdlfile_dc_1
                  + " > " + spicelogfile_dc_1)

        with open(measurefile_dc_1,'r') as fmeas:
            temp = ""
            for lineindex,line in enumerate(fmeas):
                if lineindex > 11:
                    if not line.startswith('\n'):
                        temp = temp + line.split('=')[1] + " "
                        next(fmeas) #skip the next line

            A = np.matrix(temp)
            # print(A)
            sim_count = int(simulation_list[sim_id].count[0])
            sample_count_vcm = int(simulation_list[sim_id].count[1])
            A = A.reshape(len(spec_list_dc_1),sim_count*sample_count_vcm)
            dv_matrix = A[0:round(len(spec_list_dc_1)/2), :]
            ov_matrix = A[round(len(spec_list_dc_1)/2):,:]
            # print("dv_matrix: ")
            # print("{}" .format(dv_matrix))
            # print("ov_matrix: ")
            # print("{}".format(ov_matrix))
            dv_matrix_bool = dv_matrix >= 0
            ov_matrix_bool = ov_matrix >= -0.15
            for i in range(sim_count):
                if False in dv_matrix_bool[:,i*sample_count_vcm:(i+1)*sample_count_vcm]:
                    min_icmr[param_to_vary] = i*float(simulation_list[sim_id].step[0])
                    break
                if False in ov_matrix_bool[:,i*sample_count_vcm:(i+1)*sample_count_vcm]:
                    min_icmr[param_to_vary] = i*float(simulation_list[sim_id].step[0])
                    break
    df1 = pd.DataFrame.from_dict(min_icmr, orient='index').transpose()
    fdb = fdb.append(df1, sort=True, ignore_index=True)
    fdb.to_csv("critical_range_dc_1.csv",index=False)
    if not os.path.exists("../critical_range_all"):
        os.mkdir("../critical_range_all")
    os.system("cp "+"critical_range_dc_1.csv"+" "+"../critical_range_all/critical_range_dc_1.csv")
    os.chdir(WORK_DIR)
    return []

def get_range_dc_1():
    pass
def gen_outputs_tran_1(WORK_DIR,design,simulation_list,spec_list_tran_1,param_name_list):
    os.chdir(WORK_DIR+"/sims/outputs_tran_1")
    infile_final = design + "_final.sp"
    spicelogfile = design + ".log"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    measurefile_tran_1 = design + "_tran_1.measure"
    print("Current Simulation: tran_1")
    for num, item in enumerate(simulation_list):
        if item.name == "tran_1":
            sim_id = num
            break
    temp_spec_list = list()
    for item in spec_list_tran_1:
        temp_spec_list.append(item.name)

    for item in param_name_list:
        # if node.isundertest == True:
        #     # for dev in node.devlist:
            # if node.alias != None:
            #     param_to_vary = "lp_"+node.alias
            # else :
            #     param_to_vary = "lp_"+node.name
            param_to_vary = item
            print("Variable under simulation: {}".format(param_to_vary))
            modify_mdl(param_to_vary,"tran_1",design)
            os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_tran_1+" > "+spicelogfile)
            # breakpoint()
            fdata = open(param_to_vary+".csv",'w')
            fdata_writer = csv.writer(fdata)
            fdata_writer.writerow(temp_spec_list)

            with open(measurefile_tran_1,'r') as fmeas:
                # print("row = {}, col = {}".format(len(spec_list_ac_1),scount))
                temp = ""
                sim_count = simulation_list[sim_id].count[0]
                temp_matrix = np.zeros((1,len(spec_list_tran_1)*sim_count))
                for lineindex,line in enumerate(fmeas):
                    if lineindex > 10:
                        if not line.startswith('\n'):
                            # print(line)
                            if not (line.split('=')[1].strip()=="NaN"):
                                temp = temp + line.split('=')[1] + " "
                            else:
                                temp = temp + str(-2e99) + " "
                            # temp.append(line.split('=')[1])
                A = np.matrix(temp).reshape(len(spec_list_tran_1),sim_count).transpose()

                for i in range(sim_count):
                    fdata_writer.writerow(np.array(A[i]).flat)
    os.chdir(WORK_DIR)
    pass

def get_range_tran_1(WORK_DIR,simulation_list,param_list,spec_list_tran_1):
    param_with_zero_sense = list()
    os.chdir(WORK_DIR+"/sims/outputs_tran_1")
    print("Running get_range_tran_1")
    for num, item in enumerate(simulation_list):
        if item.name == "tran_1":
            sim_id = num
            break
    fdb = pd.read_csv(WORK_DIR+"/outputs/critical_range_template.csv")
    dict_SR = {key: None for key in fdb.columns}
    # print(dict_SR)
    for p in param_list:
        # print(p.name)
        df = pd.read_csv(p.name+".csv")
        min_critval = 1e99
        if (df.loc[1,:].values - df.loc[0,:].values).sum() == 0:
            param_with_zero_sense.append(p.name)
            print(p.name)
        for item in spec_list_tran_1: # only 1 parameter for each tran_1
            # print(df[item.name])
            flag = 0
            for i in range(len(df[item.name])):
                if (df[item.name][i] < float(item.minval)) or (df[item.name][i] > float(item.maxval)):
                    flag = 1
                    if min_critval > i*float(simulation_list[sim_id].step[0]):
                        min_critval = i*float(simulation_list[sim_id].step[0])
                    break
            if flag == 0:
                if min_critval > float(simulation_list[sim_id].stop[0]):
                    min_critval = float(simulation_list[sim_id].stop[0])
        p.critval = min_critval
        dict_SR[p.name] = p.critval
    # fdb.close
    # print(dict_SR)
    df1 = pd.DataFrame([dict_SR])
    fdb = fdb.append(df1,sort=True,ignore_index=True)
    # print(df.head(6))
    fdb.to_csv("critical_range_tran_1.csv",index=False)
    if not os.path.exists("../critical_range_all"):
        os.mkdir("../critical_range_all")
    os.system("cp "+"critical_range_tran_1.csv ../critical_range_all/critical_range_tran_1.csv")
    os.chdir(WORK_DIR)
    return param_with_zero_sense
    pass

def modify_mdl(pname, sim_type, design):
    mdlfile = design + ".mdl"
    mdlfile_ac_2 = design + "_ac_2.mdl"
    mdlfile_ac_3 = design + "_ac_3.mdl"
    mdlfile_dc_1 = design + "_dc_1.mdl"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    if sim_type == "ac_1":
        fmdl = open(mdlfile,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open(mdlfile,"w")
        fmdl.write(temp)
        fmdl.close()
    elif sim_type == "dc_1":
        fmdl = open(mdlfile_dc_1,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                if a[1] != "vcm_r":
                    a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open(mdlfile_dc_1,"w")
        fmdl.write(temp)
        fmdl.close()
    elif sim_type == "tran_1":
        fmdl = open(mdlfile_tran_1,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open(mdlfile_tran_1,"w")
        fmdl.write(temp)
        fmdl.close()
    elif sim_type == "dc_2":
        fmdl = open(mdlfile_dc_2,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open("outputs_dc_2/"+mdlfile_dc_2,"w")
        fmdl.write(temp)
        fmdl.close()
    elif sim_type == "ac_2":
        fmdl = open(mdlfile_ac_2,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open(mdlfile_ac_2,"w")
        fmdl.write(temp)
        fmdl.close()
    elif sim_type == "ac_3":
        fmdl = open(mdlfile_ac_3,"r")
        temp = ""
        for line in fmdl:
            if line.startswith("foreach"):
                a = line.split(" ")
                a[1] = pname
                line = " ".join(a)
            temp = temp + line

        fmdl = open(mdlfile_ac_3,"w")
        fmdl.write(temp)
        fmdl.close()

def generate_outputs_with_paramset_ac_1(WORK_DIR, design, spec_list_ac_1, MODE):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    infile_final = design + "_for_FT.sp"
    mdlfile = design + ".mdl"
    measurefile = design + ".measure"
    spicelogfile = design + ".log"
    os.chdir(WORK_DIR+"/sims/outputs_ac_1_FT")
    print("Current simulation: ac_1")
    filenames = list()
    # if not os.path.exists("outputs_ac_1"):
    #     os.mkdir("outputs_ac_1")
    for item in spec_list_ac_1:
        filenames.append(item.name+"_"+str(MODE))
        filedata = {filename: open(filename, 'w') for filename in filenames}

    for item in spec_list_ac_1:
        filedata[item.name+"_"+str(MODE)].write(item.name+'\n')

    os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile+" > "+spicelogfile)
    with open(measurefile,"r") as fmeas:
        for line in fmeas:
            for item in spec_list_ac_1:
                if line.startswith(item.name):
                    for i in range(len(param_list)-1):
                        line=next(fmeas)
                    temp = line.split('=')[1].strip()
                    filedata[item.name+"_"+str(MODE)].write(temp+'\n')


    for file in filedata.values():
        file.close()
    os.chdir(WORK_DIR)

def generate_outputs_with_paramset_ac_2(WORK_DIR, design, spec_list_ac_2, MODE):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    infile_final = design + "_for_FT.sp"
    mdlfile_ac_2 = design + "_ac_2.mdl"
    measurefile_ac_2 = design + "_ac_2.measure"
    spicelogfile = design + ".log"
    os.chdir(WORK_DIR+"/sims/outputs_ac_2_FT")
    print("Current simulation: ac_2")
    filenames = list()
    # if not os.path.exists("outputs_ac_2"):
    #     os.mkdir("outputs_ac_2")
    print(spec_list_ac_2)
    for item in spec_list_ac_2:
        filenames.append(item.name+"_"+str(MODE))
        filedata = {filename: open(filename, 'w') for filename in filenames}

    for item in spec_list_ac_2:
        filedata[item.name+"_"+str(MODE)].write(item.name+'\n')
    print(filedata)
    os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_ac_2+" > "+spicelogfile)
    with open(measurefile_ac_2,"r") as fmeas:
        for line in fmeas:
            for item in spec_list_ac_2:
                if line.startswith(item.name):
                    for i in range(len(param_list)-1):
                        line=next(fmeas)
                    temp = line.split('=')[1].strip()
                    filedata[item.name+"_"+str(MODE)].write(temp+'\n')

    for file in filedata.values():
        file.close()

    with open("CMRR"+"_"+str(MODE),'w') as fCMRR, open("../outputs_ac_1_FT/maxgain"+"_"+str(MODE),'r') as fgain, open("CMGain"+"_"+str(MODE),'r') as fcmgain:
        fgain.readline()
        fcmgain.readline()
        fCMRR.write("CMRR\n")
        for line in fgain:
            # temp = line.split() + fgain.readline().split() + fbwout.readline().split() + fugf.readline().split() +\
            #  fgm.readline().split() + fpm.readline().split() + ficmr.readline().split() + fSR.readline().split()
            temp = float(line.split()[0]) - float(fcmgain.readline().split()[0])
            # temp = 0 - float(fcmgain.readline().split()[0])
            # print(round(temp,3))
            # print(fcmgain.readline().split()[0])
            # temp = line.split() + fgain.readline().split()
            fCMRR.write(str(round(temp,3))+'\n')

        fCMRR.close()


def generate_outputs_with_paramset_ac_3(WORK_DIR, design, spec_list_ac_3, MODE):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    infile_final = design + "_for_FT.sp"
    mdlfile_ac_3 = design + "_ac_3.mdl"
    measurefile_ac_3 = design + "_ac_3.measure"
    spicelogfile = design + ".log"
    os.chdir(WORK_DIR+"/sims/outputs_ac_3_FT")
    print("Current simulation: ac_3")
    filenames = list()
    # if not os.path.exists("outputs_ac_3"):
    #     os.mkdir("outputs_ac_3")
    for item in spec_list_ac_3:
        filenames.append(item.name+"_"+str(MODE))
        filedata = {filename: open(filename, 'w') for filename in filenames}

    for item in spec_list_ac_3:
        filedata[item.name+"_"+str(MODE)].write(item.name+'\n')
    #print(filedata)
    os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_ac_3+" > "+spicelogfile)
    with open(measurefile_ac_3,"r") as fmeas:
        for line in fmeas:
            for item in spec_list_ac_3:
                if line.startswith(item.name):
                    for i in range(len(param_list)-1):
                        line=next(fmeas)
                    temp = line.split('=')[1].strip()
                    filedata[item.name+"_"+str(MODE)].write(temp+'\n')

    for file in filedata.values():
        file.close()

    with open("PSRR"+"_"+str(MODE),'w') as fPSRR, open("../outputs_ac_1_FT/maxgain"+"_"+str(MODE),'r') as fgain, open("PSGain"+"_"+str(MODE),'r') as fpsgain:
        fgain.readline()
        fpsgain.readline()
        fPSRR.write("PSRR\n")
        for line in fgain:
            # temp = line.split() + fgain.readline().split() + fbwout.readline().split() + fugf.readline().split() +\
            #  fgm.readline().split() + fpm.readline().split() + ficmr.readline().split() + fSR.readline().split()
            temp = float(line.split()[0]) - float(fpsgain.readline().split()[0])
            # print(round(temp,3))
            # print(fcmgain.readline().split()[0])
            # temp = line.split() + fgain.readline().split()
            fPSRR.write(str(round(temp,3))+'\n')

        fPSRR.close()

def generate_outputs_with_paramset_dc_1(WORK_DIR,
                                        design,
                                        spec_list_dc_1,
                                        MODE):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    infile_final = design + "_for_FT.sp"
    mdlfile_dc_1 = design + "_dc_1.mdl"
    measurefile_dc_1 = design + "_dc_1.measure"
    spicelogfile_dc_1 = design + "_dc_1.log"
    os.chdir(WORK_DIR + "/sims/outputs_dc_1_FT")
    print("Current simulation: dc_1")
    with open("ICMR_" + str(MODE), 'w') as f:
        f.write("ICMR"+'\n')
        os.system("spectremdl -design " + infile_final + " -batch " + mdlfile_dc_1 + " > " + spicelogfile_dc_1)
        with open(measurefile_dc_1,"r") as fmeas:
            temp = ""
            for lineindex,line in enumerate(fmeas):
                if lineindex > 10:
                    # print(line)
                    if not line.startswith('\n'):
                        for i in range(len(param_list)):
                            line = next(fmeas)
                        temp = temp + line.split('=')[1] + " "
            A = np.matrix(temp)
            A = A.reshape(2,int(round(A.size/2)))
            dv_matrix = A[0,:]
            ov_matrix = A[1,:]
            rows = int(len(spec_list_dc_1)/2)
            cols = int(dv_matrix.size/rows)
            dv_matrix_reshaped = dv_matrix.reshape(rows,cols)
            ov_matrix_reshaped = ov_matrix.reshape(rows,cols)
            dv_matrix_bool = dv_matrix_reshaped >= 0
            ov_matrix_bool = ov_matrix_reshaped > -0.15
            for i in range(int(cols/2)):
                if (False in dv_matrix_bool[:,2*i:2*(i+1)]) or (False in ov_matrix_bool[:,2*i:2*(i+1)]):
                    f.write("False"+'\n')
                else:
                    f.write("True"+'\n')
    pass

def generate_outputs_with_paramset_tran_1(WORK_DIR, design, spec_list_tran_1, MODE):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    infile_final = design + "_for_FT.sp"
    mdlfile_tran_1 = design + "_tran_1.mdl"
    measurefile_tran_1 = design + "_tran_1.measure"
    spicelogfile = design + ".log"
    os.chdir(WORK_DIR+"/sims/outputs_tran_1_FT")
    print("Current simulation: tran_1")
    filenames = list()
    for item in spec_list_tran_1:
        filenames.append(item.name+"_"+str(MODE))
        filedata = {filename: open(filename, 'w') for filename in filenames}

    for item in spec_list_tran_1:
        filedata[item.name+"_"+str(MODE)].write(item.name+'\n')
    #print(filedata)
    os.system("spectremdl -design "+infile_final+ " -batch "+mdlfile_tran_1+" > "+spicelogfile)
    with open(measurefile_tran_1,"r") as fmeas:
        for line in fmeas:
            for item in spec_list_tran_1:
                if line.startswith(item.name):
                    for i in range(len(param_list)-1):
                        line=next(fmeas)
                    temp = line.split('=')[1].strip()
                    filedata[item.name+"_"+str(MODE)].write(temp+'\n')

    for file in filedata.values():
        file.close()
