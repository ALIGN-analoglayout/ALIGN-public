#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import numpy as np
import csv

def normalize_data_max_min(X):
  for i in range(np.array(X).shape[1]):
    min_v = min(X[:,i])
    max_v = max(X[:,i])
    X[:,i] = (X[:,i]-min_v)/(max_v-min_v)
  return X

read_write= csv.reader(open('rc_OTA_asap7.csv','r'))
#read_write = Read_in_File('amplifier.ma0')
data = [data for data in read_write]
#print(name)
data = np.array(data)
X=data[:,0:54]
Y=data[:,54:58]
X=np.array(X,dtype=float)
Y=np.array(Y,dtype=float)
X = normalize_data_max_min(X)
test_size = 0.7
label_name=["Gain","Unit Gain Frequency","Band Width Gain","PM"]
index = int(len(X)*test_size)
x_train = X[0:index,:]
x_test = X[index:-1,:]
y_train = Y[0:index,:]
y_test = Y[index:-1,:]

np.savez('rc_OTA_asap7.npz',X=X,Y=Y,x_train=x_train,x_test=x_test,y_train=y_train,y_test=y_test,label_name=label_name)
np.savetxt('rc_OTA_asap7_norm.csv',np.concatenate((X,Y,data[:,58:-1]),axis=1),fmt='%s',delimiter=',')






