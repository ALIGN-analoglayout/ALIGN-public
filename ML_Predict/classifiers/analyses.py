import os
import csv
import timeit
import numpy as np
import pandas as pd
import pickle
from utils.utils import scatterplot_2D
from sklearn import preprocessing
from sklearn.model_selection import train_test_split
from sklearn.decomposition import PCA
from sklearn.svm import SVC
from sklearn.naive_bayes import GaussianNB
from sklearn.neural_network import MLPClassifier
from sklearn.datasets import make_blobs
from sklearn.metrics import classification_report, confusion_matrix
from scipy.optimize import linprog
from sklearn.preprocessing import MinMaxScaler
from sklearn.multiclass import OneVsRestClassifier
from sklearn.model_selection import GridSearchCV
from sklearn.ensemble import RandomForestClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import cross_val_score

def classifier_comparison_(X_train, X_test, y_train, y_test, WORK_DIR, item):

    balance = [{0:1,1:1}, {0:1.2,1:1}, {0:1,1:1.2}]
    # print(np.unique(y, return_counts=True))
    # print('Time: ', start_time)
    param_grid = {'C': [2], 'kernel': ['linear'], 'class_weight':balance, 'gamma':['auto']}
    #grid_svc = GridSearchCV(SVC(), param_grid, scoring='accuracy', refit='accuracy', verbose=2, n_jobs=-1)
    # grid_svc.fit(X_train,y_train)

    #grid_svc = SVC(kernel='linear', class_weight='balanced', C=20)
    grid_svc = SVC(kernel='linear', class_weight={0:1,1:1}, C=2, probability=True)
    start_time = timeit.default_timer()
    grid_svc.fit(X_train,y_train)
    end_time = timeit.default_timer()
    svc_training_time = (end_time-start_time)
    print('SVC Training Time: ', svc_training_time)
    start_time = timeit.default_timer()
    clf = MLPClassifier(hidden_layer_sizes=(10,10,10), random_state=1, max_iter=1000)
    clf.fit(X_train, y_train)
    end_time = timeit.default_timer()
    mlp_training_time = (end_time-start_time)
    print('MLP Training Time: ', mlp_training_time)

    filename = WORK_DIR+"/outputs/trained_model_lsvm_"+item+".sav"
    pickle.dump(grid_svc, open(filename,'wb'))

    filename = WORK_DIR+"/outputs/trained_model_mlp_"+item+".sav"
    pickle.dump(clf, open(filename,'wb'))

    grid_predictions = grid_svc.predict(X_test)
    clf_predictions = clf.predict(X_test)


    # print("SVM:")
    # scores = cross_val_score(grid_svc, X, Y, cv=5)
    # print("Accuracy: %0.2f (+/- %0.4f)" % (scores.mean(), scores.std() * 2))
    #
    # print("MLP:")
    # scores = cross_val_score(clf, X, Y, cv=5)
    # print("Accuracy: %0.2f (+/- %0.4f)" % (scores.mean(), scores.std() * 2))


    confusion_matrix_svc = confusion_matrix(y_test,grid_predictions)
    confusion_matrix_clf = confusion_matrix(y_test,clf_predictions)

    classification_report_svc = classification_report(y_test,grid_predictions, output_dict=True)
    classification_report_clf = classification_report(y_test,clf_predictions, output_dict=True)

    return confusion_matrix_svc, confusion_matrix_clf, classification_report_svc, classification_report_clf

def analysis_with_svm(WORK_DIR, design, param_list, PoI, mode):
    tc_directory = "/" + design + "/"
    df = pd.read_csv(WORK_DIR
                     + tc_directory
                     + 'outputs/database_for_FT_' + str(mode) + '.csv')
    df_specs = pd.read_csv(WORK_DIR
                           + tc_directory
                           + "spec_limits.csv").set_index('bounds')
    X = df.loc[:, param_list].values
    # X_scaled = MinMaxScaler().fit_transform(X)
    svc_cfmatrix = {'PoI': [], 'TN': [], 'FP': [], 'FN': [], 'TP': [],\
                    'Precision': [], 'Recall': [], 'Accuracy': []}

    # print(PoI)
    # print(df.head())
    # print("Any NaN?: {}" .format(df.isnull().values.any()))
    # print("Any Inf?: {}" .format(np.isinf(df).values.any()))
    Y = df.loc[:, PoI].values
    Y_binary = np.zeros(np.shape(Y))
    if PoI == "ICMR":
        Y_binary = Y.astype(float)
        pass
    else:
        Y_binary[Y > float(df_specs.loc['min', PoI])] = 1
    X_train, X_test, y_train, y_test = train_test_split(X, Y_binary.ravel(),
                                                        test_size = 0.3)
    print(np.unique(y_train, return_counts = True))
    with open(WORK_DIR + tc_directory + 'outputs/X_train.txt', 'wb') as ftrain:
        np.savetxt(ftrain, X_train, delimiter='\t', fmt='%1.2e')
    if 0 in y_train and 1 in y_train:
        """classification with SVM"""
        balance = [{0:1, 1:1}, {0:1.2, 1:1}, {0:1, 1:1.2}]
        param_grid = {'C': [2], 'kernel': ['linear'], 'class_weight': balance,\
                      'gamma': ['auto']}
        if mode:
            grid_svc = SVC(kernel = 'linear', class_weight = 'balanced', C = 2,
                           probability = True)
        else:
            grid_svc = SVC(kernel = 'linear', class_weight = {0:1, 1:1}, C = 2,
                           probability = True)
        start_time = timeit.default_timer()
        grid_svc.fit(X_train, y_train)
        end_time = timeit.default_timer()
        svc_training_time = (end_time - start_time)
        print('SVC Training Time: ', svc_training_time)
        grid_predictions = grid_svc.predict(X_test)
        confusion_matrix_svc = confusion_matrix(y_test, grid_predictions)
        classification_report_svc = classification_report(y_test,
                                                          grid_predictions,
                                                          output_dict = True)
        print(confusion_matrix_svc)
        # print(classification_report_svc)
        accuracy = classification_report_svc['weighted avg']['f1-score']
        print(accuracy)
        if mode == 0:
            print(accuracy)
            if accuracy >= 0.95:
                print("Precision of {} with LSVM is greater than 0.95. Saving \
                       model parameters...." .format(PoI))
                filename = WORK_DIR \
                           + tc_directory \
                           + "/outputs/trained_model_lsvm_" + PoI + ".sav"
                pickle.dump(grid_svc, open(filename,'wb'))
            return accuracy

        else: # mode == 0
            print("Precision of {} with LSVM is greater than 0.90. Saving \
                   model parameters...." .format(PoI))
            filename = WORK_DIR \
                        + tc_directory \
                        + "outputs/trained_model_lsvm_" + PoI + ".sav"
            pickle.dump(grid_svc, open(filename,'wb'))
            return accuracy
    else:
        return 1


def analysis_with_mlp(WORK_DIR, design, param_list, PoI, mode):
    tc_directory = "/" + design + "/"
    df = pd.read_csv(WORK_DIR
                     + tc_directory
                     + 'outputs/database_for_FT_' + str(mode) + '.csv')
    df_specs = pd.read_csv(WORK_DIR
                           + tc_directory
                           + "spec_limits.csv").set_index('bounds')
    X = df.loc[:, param_list].values
    X_scaled = MinMaxScaler().fit_transform(X)
    clf_cfmatrix = {'PoI': [], 'TN': [], 'FP': [], 'FN': [], 'TP': [],\
                    'Precision': [], 'Recall': [], 'Accuracy': []}
    print(PoI)
    Y = df.loc[:, PoI].values
    Y_binary = np.zeros(np.shape(Y))
    if PoI == "ICMR":
        Y_binary = Y.astype(float)
        pass
    else:
        Y_binary[Y > float(df_specs.loc['min',PoI])] = 1
    X_train, X_test, y_train, y_test = train_test_split(X, Y_binary.ravel(),
                                                        test_size= 0.2)
    start_time = timeit.default_timer()
    clf = MLPClassifier(hidden_layer_sizes = (10, 10, 10),
                        random_state = 1, max_iter = 1000)
    clf.fit(X_train, y_train)
    end_time = timeit.default_timer()
    mlp_training_time = (end_time - start_time)
    print('MLP Training Time: ', mlp_training_time)
    clf_predictions = clf.predict(X_test)
    confusion_matrix_clf = confusion_matrix(y_test, clf_predictions)
    classification_report_clf = classification_report(y_test, clf_predictions,
                                                      output_dict=True)
    print("Precision of {} with LSVM is less than 0.90.\
           Saving MLP model parameters...." .format(PoI))
    filename = WORK_DIR + tc_directory + "outputs/trained_model_mlp_" + PoI + ".sav"
    pickle.dump(clf, open(filename,'wb'))
    accuracy = classification_report_clf['weighted avg']['f1-score']
    # print(accuracy)
    return accuracy

def analyses(WORK_DIR):
    df_bounds = pd.read_csv(WORK_DIR+"/outputs/node_under_test_for_smartforce.csv")
    param_list = df_bounds.columns.tolist()
    # df = pd.read_csv(WORK_DIR+'/outputs/database_for_FT.csv')
    df_specs = pd.read_csv(WORK_DIR+"/inputs/spec_limits.csv").set_index('bounds')
    headers_in_df = df.columns.tolist()
    """Use the following if alll specs are needed to be consdered"""
    PoI = [item for item in headers_in_df if item not in param_list]
    print("PoI: {}".format(PoI))
    """Use the following to explore spec selectively"""
    # PoI = ['CMRR']
    # for item in PoI:
    #     if item not in headers_in_df:
    #         logging.error("One or more items in PoI are not in database.")
    #         exit()

    """Separate inputs and outputs from the dataframe"""
    # X31 = df.loc[:, {"lp_on2_P0"}].values/df.loc[:, {"lp_on2_N0"}].values
    # X32 = df.loc[:, {"lp_VDDI_P0"}].values/df.loc[:, {"lp_VSSI_N0"}].values
    X = df.loc[:, param_list].values
    # print(X31)
    # print(X32)
    # X = np.concatenate((X31,X32), axis=1)
    print(param_list)
    # print(X)
    X_scaled = MinMaxScaler().fit_transform(X)
    """Setting up pca"""
    # pca = PCA(n_components=None, copy=True)
    pca = PCA(0.95)
    svc_cfmatrix = {'PoI':[], 'TN':[], 'FP':[], 'FN': [], 'TP':[], 'Precision':[], 'Recall':[], 'Accuracy':[]}
    clf_cfmatrix = {'PoI':[], 'TN':[], 'FP':[], 'FN': [], 'TP':[], 'Precision':[], 'Recall':[], 'Accuracy':[]}
    # print(Y_binary)
    for item in PoI:
        print(item)
        Y = df.loc[:, item].values
        Y_binary = np.zeros(np.shape(Y))
        # print("Y_binary: {}".format(Y_binary))
        if item == "ICMR":
            # print(item)
            Y_binary = Y.astype(float)
            pass
        else:
            # print("Item: {}".format(item))
            # print("Min: {}".format(df_specs.loc['min',item]))
            # print(Y)
            Y_binary[Y > float(df_specs.loc['min',item])] = 1
        # X_pca = pca.fit_transform(X)
        # print(pca.explained_variance_ratio_)
        # print("Y_binary: {}".format(Y_binary))
        X_train, X_test, y_train, y_test = train_test_split(X, Y_binary.ravel(), test_size= 0.2)
        # X_train, X_test, y_train, y_test = train_test_split(X, Y_binary.ravel(), test_size= 0.2)
        if 0 in y_train and 1 in y_train:
            print(np.unique(y_train, return_counts=True))
            # print(item)
            """classification with SVM"""
            # scatter_plot_(X[:,0],X[:,1], Y_binary)
            # scatter_plot_3D_(X[:,0],X[:,1],X[:,2], Y_binary)
            # print(X)
            # svc_classifier(X,Y_binary)
            """classification with Bayesian"""
            # bayes_classifier(X,Y_binary)

            # X_df = pd.DataFrame({'VSSI_N0': X[:, 0], 'on2_N0': X[:, 1], 'VDDI_P0': X[:, 2], 'on2_P0': X[:, 3]})
            # X_df = pd.DataFrame({'VSSI_N0': X[:, 0], 'on2_P0': X[:, 1], 'VDDI_P0': X[:, 2]})
            # X_df = pd.DataFrame({'VSSI_N0': X[:, 0], 'VDDI_P0': X[:, 1], 'on2_P0': X[:, 2]})
            # Y_df = pd.DataFrame({'Y': Y_binary})
            # pairwise_plot_(X_df,Y_df)
            # classifier_comparison_(X,Y_binary)
            confusion_matrix_svc, confusion_matrix_clf, classification_report_svc, classification_report_clf =   classifier_comparison_(X_train, X_test, y_train, y_test, WORK_DIR, item)

            print(classification_report_svc)
            svc_cfmatrix['PoI'].append(item)
            svc_cfmatrix['TN'].append(confusion_matrix_svc[0][0])
            svc_cfmatrix['FP'].append(confusion_matrix_svc[0][1])
            svc_cfmatrix['FN'].append(confusion_matrix_svc[1][0])
            svc_cfmatrix['TP'].append(confusion_matrix_svc[1][1])
            svc_cfmatrix['Precision'].append(classification_report_svc['1.0']['precision'])
            svc_cfmatrix['Recall'].append(classification_report_svc['1.0']['recall'])
            svc_cfmatrix['Accuracy'].append(classification_report_svc['weighted avg']['f1-score'])

            clf_cfmatrix['PoI'].append(item)
            clf_cfmatrix['TN'].append(confusion_matrix_clf[0][0])
            clf_cfmatrix['FP'].append(confusion_matrix_clf[0][1])
            clf_cfmatrix['FN'].append(confusion_matrix_clf[1][0])
            clf_cfmatrix['TP'].append(confusion_matrix_clf[1][1])
            clf_cfmatrix['Precision'].append(classification_report_clf['1.0']['precision'])
            clf_cfmatrix['Recall'].append(classification_report_clf['1.0']['recall'])
            clf_cfmatrix['Accuracy'].append(classification_report_clf['weighted avg']['f1-score'])

        else:
            pass
        # scatterplot_2D(X[:,0],X[:,1],Y_binary.ravel(), "n1_M2", "n1_M3")
        pass

    print("Classification report summary: SVC")
    print(pd.DataFrame.from_dict(svc_cfmatrix))
    print("Classification report summary: MLP")
    print(pd.DataFrame.from_dict(clf_cfmatrix))
