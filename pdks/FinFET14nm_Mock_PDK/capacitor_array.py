#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import math as sqrt
import numpy as np
from numpy import *
import copy
import math
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib import pyplot as patches

import json

import Evaluation_Unequal_Channel

import Layout_top_bottom_one_side_1

import Global_detailed_routing_main


class cap(object):
    a_t_h_ratio=[]

    unit_cap=5
    #w=round(sqrt(unit_cap/1.8),2)
    w=25
    num=0
    num_ratio=0
    num_h=2
    line_w=1
    line_w_2=0.5
    line_w_3=1

    # spacing=0.032
    spacing=.04
    sx=0

    h=w
    t0=0.032
    y_ppm=10**(-5)
    sy=num_h*spacing
    #sy=10
    s=0
    wire_width=0.032
    # via_width=3
    # via_height=3
    # via_color='lime'
    

    Af_1=0.0085
    cap_per_area=1.8

    metal_layer_number=7
    rho_u=0.9 
    
    res_per_length=24
    res_per_via=30
    sx=0    
    ring_name_cap=[]
    
    parasitic_wire_length_cap_low=[]
    parasitic_wire_length_cap_high=[]
    
    parasitic_wire_length_cap=[]
    connected_nodes=[]
    time_constant=0
    
    via_sx=0
    via_sy=0

    wire_length=[]
    wire_length_top=[]
    
    max_y=[]
    max_x=[]
    
    parasitic_wire_length_cap_upper=[]
    cap_per_length= 0.0085                  #parasitic cap
    cap_per_length_tb= 8.15491e-02
    cap_per_length_bottom=1.2411e-02     #M1 metal
    cap_per_length_coupling_32=7.75344e-02     #M1 metal  32nm disttance
    cap_per_length_coupling_64=5.58714e-02     #M1 metal  64nm disttance
    cap_per_length_coupling_96=4.85784e-02     #M1 metal  96nm disttance
    cap_per_length_coupling_128=3.9012e-02    #M1 metal  128nm disttance      
    cap_per_length_coupling_160=3.24968e-02   #M1 metal  160nm disttance     
    cap_per_length_coupling_192=2.78822e-02   #M1 metal  192nm disttance 
    
    coupling_cap_per_length=0          #coupling cap
    d0=1
    Parallel_wire_number  = 4
    ring_name_cap=[]
    pin_width=0
    pin_height=0
    pin_x=0
    pin_y=0    
    
    scale_factor=1000
    
    extra_track=1
    first_track_space=0
    bridge=5
    overlap=10 #nm

    
    
    def __init__(self, x_coordinate, y_coordinate, cap_name):
        self.x_coordinate=x_coordinate
        self.y_coordinate=y_coordinate
        self.cap_name=cap_name

        self.x_coordinate_new=0
        self.y_coordinate_new=0         
        self.all_marked=0
        self.counter=0
        self.ring_connected=[]
        self.branch_number=0

        self.marked=0

        self.cap_marked=0
        self.common_track_marked=0

        self.mark_now=0
        self.marked_again=0
        self.track=[]
        self.track_h=[]
        self.inter_connected=[]

        self.inter_connect=[]
       
        self.identity=[]
        self.identity_new=[]
        self.parent=0
        self.child=[]

        self.identity_n=[]
        self.identity_n.append(self.x_coordinate)
        self.identity_n.append(self.y_coordinate)
        self.identity_n.append(self.cap_name)
        
        self.share_channel=[]


        self.inter_connect_length=0
 
        
        self.track_number_mark=0
        self.track_new=[]

        self.track_left_global=[]
        self.track_right_global=[]
        self.global_route_mark=0
        self.common_track_marked_global=0
        self.connected_pins=[]

        self.top_sign=0
        self.bottom_sign=0

        self.track_left_detailed=[]
        self.track_right_detailed=[]
        self.track_detailed=[]
        
        self.track_left_detailed_top=[]
        self.track_right_detailed_top=[]
        self.track_detailed_top=[]        
        
        self.detailed_route_mark=0
        self.ratio_marked=0
        
        self.track_left_detailed=[]
        self.track_right_detailed=[]
        self.track_detailed=[]        
        self.inter_connect_length_tb=0
        self.lowest_y_j=0
        self.highest_y_j=0
        self.via_number=0
        self.selected_channel=0

        self.final_track_bottom=0
        self.final_track_top=0
        self.same_x=0
        self.flag_track_j=0
        self.connected_j_k=[]
        self.parent_j=0
        self.connected_node=0
        self.new_x=0
        self.new_y=0
        self.channel_width_l=0
        self.channel_width_r=0
        self.via_number_top=0
        self.tag=0
        self.marked_even=0
        self.marked_odd=0
        self.inter_connected_even=[]
        self.inter_connected_odd=[]
        
        


class horizontal(cap):
    
    def __init__(self, i, track_1, y_axis, x_axis, horizontal_track_new, sx, htrack):   
        self.i=i
        self.track_1=track_1
        self.y_axis=y_axis
        self.x_axis=x_axis
        self.sx=sx
        self.horizontal_track_new=[]
        self.horizontal_track_new=horizontal_track_new
        self.htrack=round(self.y_axis - cap.h/2+cap.pin_y+Layers_dict['M2']['Width']/2,5)
        self.htrack_1=round(self.y_axis + cap.h/2-cap.pin_y-Layers_dict['M2']['Width']/2,5)
        
    def horizontal_routing (self):
        self.new_f_1=0
        for n_2 in range (len(self.horizontal_track_new)):                                                    
            if abs(self.track_1-horizontal_track_new[n_2][1])<cap.w+self.sx: 
                
                if abs(self.y_axis-self.horizontal_track_new[n_2][0])<cap.h+cap.sy and self.y_axis>self.horizontal_track_new[n_2][0] and round(self.y_axis,5)==round(self.horizontal_track_new[n_2][3],5):                       
                    if round(abs(round(self.x_axis,5)-self.horizontal_track_new[n_2][2]),5)==round(cap.w+self.sx,5) and round(self.x_axis,5)!=round(self.horizontal_track_new[n_2][2],5):                                                              
                         
                        if round(self.htrack,5)==round(self.horizontal_track_new[n_2][0],5) and round(abs(self.track_1-self.horizontal_track_new[n_2][1]),5)==round(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'],5):
                            self.new_f_1=1
                            break
                        if round(self.x_axis,5)<round(self.horizontal_track_new[n_2][2],5) and self.track_1>round(self.horizontal_track_new[n_2][1],5):
                            self.new_f_1=1
                            break
                        if round(self.x_axis,5)>round(self.horizontal_track_new[n_2][2],5) and self.track_1<round(self.horizontal_track_new[n_2][1],5):
                            self.new_f_1=1
                            break
                        
        return self.new_f_1
    
    def horizontal_routing_top (self):
        self.new_f_1=0
        for n_2 in range (len(self.horizontal_track_new)):                                                    
            if abs(self.track_1-self.horizontal_track_new[n_2][1])<cap.w+self.sx:
                                                                                
                if abs(self.y_axis-self.horizontal_track_new[n_2][0])<cap.h+cap.sy and self.y_axis<self.horizontal_track_new[n_2][0] and round(self.y_axis,5)==round(self.horizontal_track_new[n_2][3],5):  
                    if round(abs(round(self.x_axis,5)-self.horizontal_track_new[n_2][2]),5)==round(cap.w+self.sx,5) and round(self.x_axis,5)!=round(self.horizontal_track_new[n_2][2],5):                                                              
                             
                        if round(self.htrack_1,5)==round(self.horizontal_track_new[n_2][0],5) and round(abs(round(self.track_1,5)-round(self.horizontal_track_new[n_2][1],5)),5)==round(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'],5):
                            self.new_f_1=1                             
                            break
                        if round(self.x_axis,5)<round(self.horizontal_track_new[n_2][2],5) and self.track_1>round(self.horizontal_track_new[n_2][1],5):
                            self.new_f_1=1
                            break
                        if round(self.x_axis,5)>round(self.horizontal_track_new[n_2][2],5) and self.track_1<round(self.horizontal_track_new[n_2][1],5):
                            self.new_f_1=1
                            break

        return self.new_f_1 

    def horizontal_routing_top_Split (self):
        self.new_f_1=0

        for n_2 in range (len(self.horizontal_track_new)):                                                    
            if abs(self.track_1-self.horizontal_track_new[n_2][1])<cap.w+self.sx:
                                                                                
                if abs(self.y_axis-self.horizontal_track_new[n_2][0])<cap.h+cap.sy and self.y_axis<self.horizontal_track_new[n_2][0] and round(self.y_axis,5)==round(self.horizontal_track_new[n_2][3],5):  
                    if round(abs(round(self.x_axis,5)-self.horizontal_track_new[n_2][2]),5)==round(cap.w+self.sx,5) and round(self.x_axis,5)!=round(self.horizontal_track_new[n_2][2],5):                                                              
  
                        even_odd_flag=0
                        if (int(self.horizontal_track_new[n_2][4]-1))%2==0 and self.i%2!=0:
                            even_odd_flag=1

                        if (int(self.horizontal_track_new[n_2][4]-1))%2!=0 and self.i%2==0:
                            even_odd_flag=1
                            
                        if round(self.htrack_1,5)==round(self.horizontal_track_new[n_2][0],5) and round(abs(round(self.track_1,5)-round(self.horizontal_track_new[n_2][1],5)),5)==round(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'],5) and even_odd_flag==1:
                            self.new_f_1=1                                                
                            break
                        if round(self.x_axis,5)<round(self.horizontal_track_new[n_2][2],5) and self.track_1>round(self.horizontal_track_new[n_2][1],5)  and even_odd_flag==1:
                            self.new_f_1=1 
                            break
                        if round(self.x_axis,5)>round(self.horizontal_track_new[n_2][2],5) and self.track_1<round(self.horizontal_track_new[n_2][1],5) and even_odd_flag==1:
                            self.new_f_1=1                           
                            break 
                        
        return self.new_f_1
    
    def horizontal_track_assign(self):
        # self.htrack=self.y_axis - cap.h/2+Layers_dict['M2']['Width']/2+cap.pin_y-Layers_dict['M2']['Space']-Layers_dict['M2']['Width']
        self.htrack=self.y_axis - cap.h/2-Layers_dict['M2']['Space']-Layers_dict['M2']['Width']/2
        return self.htrack      

    def horizontal_track_assign_top(self):
        self.htrack=self.y_axis + cap.h/2+Layers_dict['M2']['Space']+Layers_dict['M2']['Width']/2
        return self.htrack 

    def insert(self, htrack):
        h_t=[]
        h_t.append(round(htrack,5))
        h_t.append(round(self.track_1,5))
        h_t.append(self.x_axis)
        h_t.append(self.y_axis)         
        return h_t  

class channel():    
    def __init__(self, x_axis):   
        self.x_axis=x_axis
        self.track_left=[]
        self.track_right=[]
  

def Metal_layer_information(k):
    M1={}
    M1['Direction']=k['Direction']
    M1['Space']=(k['Pitch']-k['Width'])
    M1['Width']=k['Width']
    M1['Color']=k['Color'] 
    return M1

def Via_layer_information(k):
    V1={}
    V1['WidthX']=k['WidthX']
    V1['WidthY']=k['WidthY']
    V1['VencA_L']=k['VencA_L']
    V1['VencA_H']=k['VencA_H']
    V1['VencP_L']=k['VencP_L']
    V1['VencP_H']=k['VencP_H']
    #V1['Color']=k['Color'] 
    
    return V1

Layers_dict={}

with open('layers.json', "rt") as fp:
    j = json.load(fp)
    for i in range (len(j['Abstraction'])):
        if j['Abstraction'][i]['Layer']=='M1': 
            Layers_dict['M1']=Metal_layer_information(j['Abstraction'][i])
        if j['Abstraction'][i]['Layer']=='V0': 
            Layers_dict['V1']=Via_layer_information(j['Abstraction'][i])
        if j['Abstraction'][i]['Layer']=='M2': 
            Layers_dict['M2']=Metal_layer_information(j['Abstraction'][i])
        if j['Abstraction'][i]['Layer']=='V1': 
            Layers_dict['V2']=Via_layer_information(j['Abstraction'][i])
        if j['Abstraction'][i]['Layer']=='M3': 
            Layers_dict['M3']=Metal_layer_information(j['Abstraction'][i])                               

strToFind='SIZE' 
pin_plus='PORT'
rect='RECT'

#pin_minus='PIN MINUS'

with open('CAP_12F.lef') as f:
#with open('test.lef') as f:
    flag_found=0
    flag_found_1=0
    for line in f:
        if strToFind in line:
            res = [int(i) for i in line.split() if i.isdigit()]                        
            cap.w=res[0]
            cap.h=res[1]
            flag_found=1
        if pin_plus in line:
            for line_2 in f:
                if rect in line_2:
                    res = [int(i) for i in line_2.split() if i.isdigit()] 
                    #print('res', res, line_2, line, rect)                       
                    cap.pin_width=(res[2]-res[0])
                    cap.pin_height=(res[3]-res[1])
                    cap.pin_x=res[0]
                    cap.pin_y=res[1]             
                    flag_found_1=1
                    break
        if flag_found==1 and flag_found_1==1:
            break

              
list1=[]
#space_requirement, bit_num = input ("Enter space requirement and number of capacitors: ").split()


space_requirement='Equal'
#bit_num=''

input_string = input("Enter a list element separated by space: ")
#list1  = input_string.split()

# list1 = list(map(int,input("Enter the ratios: ").strip().split()))[:int(bit_num)+1]
list1 = list(map(int,input_string.split()))

circuit_type='General'
count_bit=0
for i in range (len(list1)):
    if list1[i]%2==0:        
        if i!=0 and list1[i]==2*list1[i-1]:                        
            count_bit=count_bit+1

if count_bit==len(list1)-2 and list1[0]%2!=0 and list1[1]%2!=0:
    circuit_type='Binary'
    
if count_bit==len(list1)-2 and list1[0]%2==0 and list1[1]%2==0:
    circuit_type='Binary'  
        
count_split=0    
if list1[0]==list1[1]==list1[2]==1 and list1[3]==list1[4]==list1[5]==2:
    for i in range (6, len(list1)-1, 2):
        if list1[i]%2==0 and list1[i+1]%2==0 and list1[i]==list1[i+1] : 
            count_split=count_split+1
            
if count_split==len(list1)-6-(len(list1)-6)//2 and count_split!=0:
    circuit_type='Split'



Terminal_list=[]


        
new_list=copy.deepcopy(list1)

#if len(new_list)

Device_Name=[]

for i in range (len(list1)):
    Device_Name.append(i+1)
   
def takeSecond(elem):
    return elem[1] 

LSB_length=0
MSB_length=0
if circuit_type=='Binary':
    if len(new_list)==7:
        cap.time_constant=5.55
    elif len(new_list)==8:
        cap.time_constant=6.24
    elif len(new_list)==9:
        cap.time_constant=6.8
    elif len(new_list)==10:
        cap.time_constant=7.62
    elif len(new_list)==11:
        cap.time_constant=8.32
    elif len(new_list)==12:
        cap.time_constant=6.8
    elif len(new_list)==13:
        cap.time_constant=7.62
    elif len(new_list)==14:
        cap.time_constant=8.32
        
elif circuit_type=='Split':
    if len(new_list)==8:
        cap.time_constant=5.55
        LSB_length=4
        MSB_length=3        
    elif len(new_list)==9:
        cap.time_constant=6.24
        LSB_length=4
        MSB_length=4        
    elif len(new_list)==10:
        cap.time_constant=6.8
        LSB_length=5
        MSB_length=4        
    elif len(new_list)==11:
        cap.time_constant=7.62
        LSB_length=5
        MSB_length=5        
    elif len(new_list)==12:
        cap.time_constant=8.32
        LSB_length=6
        MSB_length=5        
    elif len(new_list)==13:
        cap.time_constant=9.01
        LSB_length=6
        MSB_length=6        
    elif len(new_list)==14:
        cap.time_constant=9.704
        LSB_length=7
        MSB_length=6        
    elif len(new_list)==15:
        cap.time_constant=10.4
        LSB_length=7
        MSB_length=7        
    elif len(new_list)==16:
        cap.time_constant=11.1
        LSB_length=8
        MSB_length=7        
    
# color_py=['indigo', 'b', 'm', 'g', 'darkcyan', 'cyan','limegreen',  'r','darkgrey','darkcyan','grey',    'magenta']

color_py=['indigo', 'b', 'm', 'limegreen', 'darkcyan', 'grey','darkcyan',  'deeppink','grey','darkcyan','grey',    'magenta', 'k', 'pink', 'r', 'b', 'g', 'grey']


color_mat=['r', 'r', 'k','k']
my_color=[]

for i in range (len(Device_Name)):
    my_color.append(color_py[i])

# aspect_ratio=cap.w/cap.h
aspect_ratio=1
a=sum(list1)
r = math.ceil(sqrt(a*aspect_ratio))      #row size calculation
c=math.ceil(a/r)            #colomn size calculation

a=int(r/2)
r_mid=int(r/2)
only_odd=[num for num in list1 if num %2 == 1]

row=copy.deepcopy(r)
colomn=copy.deepcopy(c)
# row=8
# colomn=4

z=0
odd_count=0
last_odd=0
for i in range (len(list1)):
    if list1[i]%2!=0:
        odd_count=odd_count+1
        last_odd=i+1    

a4=(colomn+1)/2-1
a3=(row+1)/2-1 
mat = np.zeros((row,colomn))

sum_n=row*colomn
n=math.ceil((row*colomn)/2)

pair_mat=np.zeros((n,2))
x=0 
y=0 
d=0 
c=0 
s=1 
size=0
if row>colomn:    
    size=colomn 
else: 
    size=row

x=(colomn-1)//2
y=(row-1)//2
  
mat = np.zeros((row,colomn))


#Pair matrix formation

if row%2!=0 and colomn%2!=0 and odd_count!=0 and odd_count%2!=0:
    list1[0]=list1[0]-1

len_p=0
p_k=0
flag_mat=0

if row%2!=0 and colomn%2!=0 and odd_count!=0 and odd_count%2!=0:
    flag_mat=1
    
flag_pair=0
if row%2==0 and colomn%2==0:
    flag_pair=1
if row%2!=0 and colomn%2==0:
    flag_pair=1
if row%2==0 and colomn%2!=0:
    flag_pair=1

bridge_first=0
if row%2!=0 and colomn%2!=0:
    bridge_first=1
if circuit_type=='Split' and bridge_first==0: 
    pair_mat[len_p][0]=cap.bridge+1 
    pair_mat[len_p][1]=cap.bridge+1 
    len_p=len_p+1    
    
loop_count_p=0
for i in range (len(list1)):
    if list1[i]%2!=0:        
        pair_mat[len_p][p_k]=i+1
        list1[i]=list1[i]-1
        p_k=p_k+1
        loop_count_p=loop_count_p+1
        if   flag_pair==1 and odd_count%2!=0 and i+1==last_odd:
            
            pair_mat[len_p][p_k]=0
            p_k=p_k+1
            
        if p_k>1:
            p_k=0
            len_p=len_p+1

for i in range (len(list1)):
    for j in range (list1[i]):
        if circuit_type=='Split' and bridge_first==0:
            if list1[i]!=0 and i!=cap.bridge:
                pair_mat[len_p][0]=i+1
                pair_mat[len_p][1]=i+1
                list1[i]=list1[i]-2
                len_p=len_p+1
        else:
            if list1[i]!=0:
                pair_mat[len_p][0]=i+1
                pair_mat[len_p][1]=i+1
                list1[i]=list1[i]-2
                len_p=len_p+1 


#Common centroid Placement
        
n_k=0 
flag_mat=0
if row%2!=0 and odd_count!=0 and odd_count%2!=0:
    flag_mat=1
elif row%2!=0 and colomn%2!=0 and odd_count!=0 and odd_count%2==0:
    flag_mat=1
 
for k in range (size):
    j_range=2
    if k<size-1:
        j_range=2
    else:
        j_range=1
    
    for j in range (j_range):
        for i in range (s): 
            if flag_mat==1:
                flag_mat=0
                if row%2!=0 and colomn%2!=0 and odd_count!=0 and odd_count%2!=0:
                    mat[y][x] = Device_Name[0]
                elif row%2!=0 and colomn%2!=0 and odd_count!=0 and odd_count%2==0:
                    mat[y][x]=0  
            else:
                if mat[y][x]==0 and mat[row-y-1][colomn-x-1]==0 and n_k<len(pair_mat): 
                    mat[y][x]=pair_mat[n_k][0]
                    mat[row-y-1][colomn-x-1]=pair_mat[n_k][1]
                    n_k=n_k+1

          
            if d==0:
                y=y+1
            elif d==1: 
                x=x+1
            elif d==2:
                y=y-1
            elif d==3:
                x=x-1

        d=(d+1)%4        
    s=s+1
    


if row!=colomn:
    if row>colomn:

        for j in range ((row-colomn)//2+1):
            if y<row and row-y-1<row:
            
                if j%2==0:
                    
                    for i in range (colomn):
                        if mat[y][i]==0 and mat[row-y-1][colomn-i-1]==0 and n_k<len(pair_mat):                
                            mat[y][i]=pair_mat[n_k][0]
                            mat[row-y-1][colomn-i-1]=pair_mat[n_k][1]
                            
                            n_k=n_k+1
                    if y>row//2:
                        y=y+1
                    else:
                        y=y-1
                else:
                    for i in range (colomn-1, -1,-1):
                        if mat[y][i]==0 and mat[row-y-1][colomn-i-1]==0 and n_k<len(pair_mat):                
                            mat[y][i]=pair_mat[n_k][0]
                            mat[row-y-1][colomn-i-1]=pair_mat[n_k][1]
                            n_k=n_k+1 
                    if y>row//2:
                        y=y+1
                    else:
                        y=y-1             
    else:
        for j in range ((colomn-row)//2+1):
            if y<colomn and colomn-x-1<colomn:
                if j%2==0:
                    for i in range (row):
                        if mat[i][x]==0 and mat[row-i-1][colomn-x-1]==0 and n_k<len(pair_mat):                         
                            mat[i][x]=pair_mat[n_k][0]
                            mat[row-i-1][colomn-x-1]=pair_mat[n_k][1]
                            n_k=n_k+1 
                            
                    if x>colomn//2:
                        x=x+1
                    else:
                        x=x-1
                else:
                    for i in range (row-1, -1, -1):
                        if mat[i][x]==0 and mat[row-i-1][colomn-x-1]==0 and n_k<len(pair_mat):                         
                            mat[i][x]=pair_mat[n_k][0]
                            mat[row-i-1][colomn-x-1]=pair_mat[n_k][1]
                            n_k=n_k+1 
                    if x>colomn//2:
                        x=x+1
                    else:
                        x=x-1


device_list=[]
distance=[]
point=[]
for D in Device_Name:    
    for i in range (row):    
        for j in range (colomn):
            if mat[i][j]==D:
                point_property=[]
                device_list.append(D)
                point_property.append(i)
                point_property.append(j)
                point_property.append(D)
                point.append(point_property)


device_unique=set(device_list)
device_unique_1=list(device_unique)
device_unique_1.sort()



eq_1=[]

for i in range(len(device_unique_1)):
    same_capacitor_point=[]
    for j in range (len(point)):
        if (point[j][2]==device_unique_1[i]):
            same_capacitor_point.append(point[j])            
    eq_1.append(same_capacitor_point)

#Evaluation
common_centroid_point=Evaluation_Unequal_Channel.common_centroid_point_calculation(eq_1, row, colomn)
(correlation_coeff, corr_var, un_corr_var, Rho_avg, Var_ct)=Evaluation_Unequal_Channel.correlation_coefficient(eq_1, cap.Af_1, cap.unit_cap, new_list, cap.rho_u, cap.d0)     
Sigma=Evaluation_Unequal_Channel.Sigma_C(eq_1, cap.Af_1, cap.unit_cap, cap.rho_u, cap.cap_per_area, cap.w, cap.h, cap.d0)           

#Object creation       
obj=[]
for i in range (len(eq_1)):
    q=[]
    for j in range (len(eq_1[i])):
        q.append(cap(eq_1[i][j][1], eq_1[i][j][0], eq_1[i][j][2]))
    obj.append(q)

obj_channel=[]
for i in range (colomn):
    obj_channel.append(channel(i))


LSB_count=0
MSB_count=0
already_listed_LSB=[]
already_listed_MSB=[]
if circuit_type =='Split':
    for i in range (len(obj)):    
        for j in range (len(obj[i])):
            #if i!=cap.bridge:
                #print('LSB_count<=int(LSB_length)', LSB_count, i)
            if i%2==0 and LSB_count<=int(LSB_length) and i not in already_listed_LSB:
                obj[i][j].tag='LSB'
                LSB_count=LSB_count+1
                already_listed_LSB.append(i)
            if i%2!=0 or LSB_count>int(LSB_length) and i not in already_listed_MSB:
                obj[i][j].tag='MSB'
                MSB_count=MSB_count+1
                already_listed_MSB.append(i)

#Interconnected capacitor group formation
for i in range (len(obj)):    
    for j in range (len(obj[i])): 
        if obj[i][j].track_number_mark==1:
            continue        

        obj[i][j].inter_connect.append(obj[i][j].identity_n) 
        stack=[]
        stack.append(obj[i][j].identity_n)
        p=0
        while (len(stack)!=0): 
            obj[i][j].track_number_mark=1
            for k in range (len(obj[i])):                     
                d=((stack[p][0]-obj[i][k].x_coordinate)**2+(stack[p][1]-obj[i][k].y_coordinate)**2)**(1/2)                               
                if d==1:
                    
                    if obj[i][k].track_number_mark==0:
                        new_k=0
                        for q in range (len(obj[i])):
                            if stack[p]==obj[i][q].identity_n:
                                new_k=q

                        obj[i][k].track_number_mark=1
                        stack.append(obj[i][k].identity_n)  
                        
                        obj[i][j].inter_connect.append(obj[i][k].identity_n)                 
            stack.pop(0)

#Finding out all connected capacitor groups
All_conn=[]               
for i in range (len(obj)):
    for j in range (len(obj[i])):
        if len(obj[i][j].inter_connect)!=0:
            if len(obj[i][j].inter_connect) == new_list[i] and len(obj[i][j].inter_connect)!=1 and len(obj[i][j].inter_connect)!=2 :
                All_conn.append(i+1)

#Global track creation

max_track=20

first_init=0
init=max_track
for col in range (colomn):                
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            if obj[i][j].x_coordinate==col:
                for k in range (first_init, init):                   
                    obj[i][j].track_left_global.append(k)
                for k in range (init, init+max_track):                       
                    obj[i][j].track_right_global.append(k)
    
    first_init= init              
    init=init+max_track                

x_cor=[]
for col in range (colomn): 
    br_c=0               
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            if obj[i][j].x_coordinate==col:
                br_c=1
                break
        if br_c==1:
            break

new_at=[]    
for i in range (len(obj)):
    for j in range (len(obj[i])-1):
        for k in range (j+1, len(obj[i])):             
            flag_1=0
            if len(obj[i][j].inter_connect)!=0 and len(obj[i][k].inter_connect)!=0 :                                      
                for rr in range (len(obj[i])):
                    if obj[i][rr].identity_n in obj[i][k].inter_connect:          
                        for rr_1 in range (len(obj[i])):
                            if obj[i][rr_1].identity_n in obj[i][j].inter_connect:                                 
                                if obj[i][rr_1].x_coordinate == obj[i][rr].x_coordinate or abs(obj[i][rr_1].x_coordinate-obj[i][rr].x_coordinate)==1 :                                            
                                    flag_1=1
                                    obj[i][j].common_track_marked_global=1
                                    obj[i][k].common_track_marked_global=1
                                    obj[i][k].share_channel.append(j)
                                    obj[i][j].share_channel.append(k)

                                    if flag_1==1:
                                        break                    

                        if flag_1==1:
                            break


#Performing Global routing 

global_track=[]
distance_list_all=[]
top_bot_both=[]
top_top_bottom_bottom=[] 

distance_equal_list=[]
i_list_distance_eq=[]
j_list_distance_eq=[]
k_list_distance_eq=[]
already_listed=[]
flag_third=0


same_x_values=[]

if circuit_type=='Split':
    for i in range (len(obj)):
        if i==cap.bridge:
            for j in range (len(obj[i])):
                if len(obj[i][j].inter_connect)==new_list[i]:
                    obj[i][j].global_route_mark=1
                    obj[i][j].detailed_route_mark=1

        
Dis_list_all=[]
for i in range (len(obj)):
    flag_done=0
    for j in range (len(obj[i])):
 
        
        
        flag=0
        if len(obj[i][j].inter_connect)!=0  and obj[i][j].global_route_mark==0:
            
            if len(obj[i][j].inter_connect)!=new_list[i]:                  
                if obj[i][j].common_track_marked_global!=0  and obj[i][j].global_route_mark==0 :
                    ind_j=0
                    possible_connection=[]
                    x_mirror=colomn-obj[i][j].x_coordinate-1
                    y_mirror=row-obj[i][j].y_coordinate-1
                    
                    (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)                     
                    
                    j_index=obj[i_index][j_index].parent_j
                    
                    if obj[i][j_index].global_route_mark!=0:
                        j_index_mirror=obj[i][j_index].connected_j_k[0]
                        k_index_mirror=obj[i][j_index].connected_j_k[1]
                        
                        x_mirror_1=colomn-obj[i][j_index_mirror].x_coordinate-1
                        y_mirror_1=row-obj[i][j_index_mirror].y_coordinate-1
                        
                        (i_index_1, j_index_1)=Global_detailed_routing_main.capacitor_index(obj, x_mirror_1, y_mirror_1)   
                        ind_j=j_index_1
                    
                        x_mirror_2=colomn-obj[i][k_index_mirror].x_coordinate-1
                        y_mirror_2=row-obj[i][k_index_mirror].y_coordinate-1
                        
                        (i_index_2, k_index_1)=Global_detailed_routing_main.capacitor_index(obj, x_mirror_2, y_mirror_2)
                        
                       
                    
                    for_print=[]
                    
                    y_list=[]
                    x_list=[]

                    for t in range (len(obj[i][j].inter_connect)):                                                    
                        y_list.append(obj[i][j].inter_connect[t][1])
                        x_list.append(obj[i][j].inter_connect[t][0]) 
                        

                    flag_j=0
                    
                    d_l=[] 

                    for k in range (len(obj[i])):                        
                        if j!=k and len(obj[i][k].inter_connect)!=0 and obj[i][k].global_route_mark==0 :
                            y_list_1=[]
                            x_list_1=[]
            
                            for t_1 in range (len(obj[i][k].inter_connect)):
                                y_list_1.append(obj[i][k].inter_connect[t_1][1])
                                x_list_1.append(obj[i][k].inter_connect[t_1][0])

                            dis_list=[]
                      
                            if flag_j==0:
                                for y_v_j in range (len(y_list)):
                                    for y_v_k in range (len(y_list_1)):

                                        dis=((x_list[y_v_j]-x_list_1[y_v_k])**2+(y_list[y_v_j]-y_list_1[y_v_k])**2)**(1/2)
                                          
                                        temp=[]
                                        temp.append(abs(dis))
                                        temp.append(y_list[y_v_j])
                                        temp.append(x_list[y_v_j])
                                        temp.append(y_list_1[y_v_k])
                                           
                                        temp.append(x_list_1[y_v_k])
                                        dis_list.append(temp)                            
                            else:                                   
                                for y_v_k in range (len(y_list_1)):
                                    dis=((obj[i][ind_j].x_coordinate-x_list_1[y_v_k])**2+(obj[i][ind_j].y_coordinate-y_list_1[y_v_k])**2)**(1/2)
                                    temp=[]
                                    temp.append(abs(dis))
                                    temp.append(obj[i][ind_j].y_coordinate)
                                    temp.append(obj[i][ind_j].x_coordinate)
                                    temp.append(y_list_1[y_v_k])                                       
                                    temp.append(x_list_1[y_v_k])
                                    
                                    dis_list.append(temp) 
                                    
                            dis_list.sort(key = lambda dis_list: dis_list[0])
                            y_min_cal_j_r=dis_list[0][1]
                            y_min_cal_k_r=dis_list[0][3]
                            x_min_1=dis_list[0][2]
                            x_min_2=dis_list[0][4]
                            y_min_cal_j_r_2=0
                            y_min_cal_k_r_2=0

                            d_count=0
                            distance_equal=[]
                            flag_dis=0                            
                            for l in range (len(dis_list)):  
                                if (dis_list[l][2]-dis_list[l][4])==0:   
                                    d_count=d_count+1
                                    distance_equal.append(dis_list[l]) 
                                    flag_dis=1

                                    

                                
                            for l in range (len(dis_list)):
                                if (dis_list[l][2]-dis_list[l][4])==0 or (dis_list[l][2]-dis_list[l][4])==1 or (dis_list[l][2]-dis_list[l][4])==-1:                            
                                    y_min_cal_j_r=dis_list[l][1]
                                    y_min_cal_k_r=dis_list[l][3]
                                    x_min_1=dis_list[l][2]
                                    x_min_2=dis_list[l][4]
                                    
                                    for ll in range (l+1, len(dis_list)): 
                                        if abs(dis_list[ll][2]-dis_list[ll][4])==abs(dis_list[l][2]-dis_list[l][4]) and dis_list[l][0]==dis_list[0][0] and dis_list[ll][0]==dis_list[0][0] :                                            
                                            d_count=1
                                            if dis_list[ll][1]>dis_list[l][1] and  dis_list[ll][3]>dis_list[l][3]:
                                                y_min_cal_j_r=dis_list[ll][1]
                                                y_min_cal_k_r=dis_list[ll][3]
                                                x_min_1=dis_list[ll][2]
                                                x_min_2=dis_list[ll][4] 
                                                
                                                break
                                            


                                    if (dis_list[l][2]-dis_list[l][4])==0 and d_count==1 and dis_list[l][0]!=dis_list[0][0]:
                                        d_count=2
                                        distance_equal.append(dis_list[l]) 

                                    elif (dis_list[l][2]-dis_list[l][4])==1 and d_count>1 and dis_list[l][0]==dis_list[0][0]:
                                        d_count=1                                       
                                    elif (dis_list[l][2]-dis_list[l][4])==-1 and d_count>1 and dis_list[l][0]==dis_list[0][0]:
                                        d_count=1                                        
                                    break


                            ind_k=0
                            
                            if flag_j==0:
                                for rr_1 in range (len(obj[i])):
                                    if obj[i][rr_1].identity_n in obj[i][j].inter_connect:  
                                        if obj[i][rr_1].y_coordinate==y_min_cal_j_r and obj[i][rr_1].x_coordinate==x_min_1:
                                            ind_j=rr_1
                                            break                         
                           
                           
                            for rr in range (len(obj[i])):
                                if obj[i][rr].identity_n in obj[i][k].inter_connect : 
                                    if obj[i][rr].y_coordinate==y_min_cal_k_r and obj[i][rr].x_coordinate==x_min_2:
                                        ind_k=rr   
                                        break

                            if (obj[i][ind_j].x_coordinate-obj[i][ind_k].x_coordinate)==0 or (obj[i][ind_j].x_coordinate-obj[i][ind_k].x_coordinate)==1 or (obj[i][ind_j].x_coordinate-obj[i][ind_k].x_coordinate)==-1:
                                do_it=0 
                                flag_j=1  
                                l_list=[]
                                l_list.append(ind_j)
                                l_list.append(ind_k)
                                possible_connection.append(l_list)
                                obj[i][j].connected_j_k.append(ind_j)
                                obj[i][j].connected_j_k.append(ind_k)
                                
                                obj[i][k].connected_j_k.append(ind_k)
                                obj[i][k].connected_j_k.append(ind_j)
                                
                    Dis_list_all.append(d_l)

                    if  len(possible_connection)!=0 and flag_done==0: 
                        
                        count_index=[]
                        tracker=[]
                        for p_c in range (len(possible_connection)-1): 
                            cnt=1
                            for p_a in range (p_c+1, len(possible_connection)):
                                if possible_connection[p_c][0]==possible_connection[p_a][0] and possible_connection[p_c][0] not in tracker:
                                    cnt=cnt+1
                            
                            if possible_connection[p_c][0] not in tracker:
                                idx_count=[]
                                idx_count.append(possible_connection[p_c][0])
                                idx_count.append(cnt)
                                count_index.append(idx_count)
                                tracker.append(possible_connection[p_c][0])
                        
                        ind_j_r=0

                        if len(count_index)>1:
                            n_list=[]
                            for c_p in range (len(count_index)):
                                n_list.append(count_index[c_p][1])
                            max_l=max(n_list)
                            for c_p in range (len(count_index)):
                                if count_index[c_p][1]==max_l:
                                    ind_j_r=count_index[c_p][0]                                    
                                    break
                        elif len(count_index)==1:
                            ind_j_r=count_index[0][0]
                        elif len(count_index)==0:                            
                            ind_j_r=possible_connection[0][0]
                        
                        cap_count_left=0
                        cap_count_right=0
                        within_column_sel_left=[]
                        within_column_sel_right=[]
                        left_channel_index=[]
                        right_channel_index=[]                        
                        for n_p in range (len(possible_connection)): 
                            l_flag=0
                            if possible_connection[n_p][0]==ind_j_r and obj[i][possible_connection[n_p][1]].global_route_mark==0 :                                
                                if (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p][1]].x_coordinate)==0  or (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p][1]].x_coordinate)==1:                                     
                                    cap_count_left=cap_count_left+2
                                    within_column_sel_left.append(possible_connection[n_p][1])
                                    left_channel_index.append(possible_connection[n_p][1])
                                    l_flag=1

                                    for n_p_1 in range (len(possible_connection)):
                                        if n_p!=n_p_1 and possible_connection[n_p_1][0]==ind_j_r  and possible_connection[n_p_1][1] not in within_column_sel_left and obj[i][possible_connection[n_p_1][1]].global_route_mark==0:
                                            if (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p_1][1]].x_coordinate)==0  or (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p_1][1]].x_coordinate)==1:
                                                cap_count_left=cap_count_left+1
                                                within_column_sel_left.append(possible_connection[n_p_1][1])
                                                left_channel_index.append(possible_connection[n_p_1][1])
                            if l_flag==1:
                                break

                        for n_p in range (len(possible_connection)): 
                            r_flag=0
                            if possible_connection[n_p][0]==ind_j_r  and obj[i][possible_connection[n_p][1]].global_route_mark==0 :                                
                                if (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p][1]].x_coordinate)==0 or (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p][1]].x_coordinate)==-1:
                                    cap_count_right=cap_count_right+2
                                    within_column_sel_right.append(possible_connection[n_p][1])
                                    right_channel_index.append(possible_connection[n_p][1])
                                    r_flag=1

                                    for n_p_1 in range (len(possible_connection)):
                                        if n_p!=n_p_1 and possible_connection[n_p_1][0]==ind_j_r  and possible_connection[n_p_1][1] not in within_column_sel_right and obj[i][possible_connection[n_p_1][1]].global_route_mark==0:
                                            if (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p_1][1]].x_coordinate)==0  or (obj[i][ind_j_r].x_coordinate-obj[i][possible_connection[n_p_1][1]].x_coordinate)==-1:
                                                cap_count_right=cap_count_right+1
                                                within_column_sel_right.append(possible_connection[n_p_1][1])
                                                right_channel_index.append(possible_connection[n_p_1][1])
                            if r_flag==1:
                                break

                        x_mirror=colomn-obj[i][ind_j_r].x_coordinate-1
                        y_mirror=row-obj[i][ind_j_r].y_coordinate-1 

                        (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)
                        
                        if obj[i_index][j_index].global_route_mark==1:
                            if obj[i_index][j_index].top_sign==1 and cap_count_left<cap_count_right:
                                cap_count_left=cap_count_right+1

                        x_j=obj[i][ind_j_r].x_coordinate
                        cap_count_same_x=0
                        for index_c in left_channel_index:
                            if obj[i][index_c].x_coordinate==x_j:
                                cap_count_same_x=cap_count_same_x+1
                        
                        if circuit_type=='General':
                            if cap_count_same_x==len(right_channel_index) and x_j<a4  and cap_count_left==cap_count_right:
                                Global_detailed_routing_main.Right_shared_channel_span(obj, max_track, i, j, ind_j_r, global_track, right_channel_index)                             
                                obj[i][j].same_x=1   
                            if cap_count_same_x==len(left_channel_index) and x_j>a4 and cap_count_left==cap_count_right:
                                Global_detailed_routing_main.Left_shared_channel_span(obj, max_track, i, j, ind_j_r, global_track, left_channel_index)                            
                                obj[i][j].same_x=1

                        same_x_flag=0
                        if cap_count_left==cap_count_right and obj[i][possible_connection[0][1]].x_coordinate==obj[i][ind_j_r].x_coordinate and obj[i][ind_j_r].global_route_mark==0 :
                            
                            same_x_v=[]
                            same_x_v.append(i)
                            same_x_v.append(j)
                            same_x_v.append(ind_j_r)
                            same_x_v.append(left_channel_index)                            
                            same_x_values.append(same_x_v)
                            same_x_flag=1
                            

                                                
                        if cap_count_left>=cap_count_right and obj[i][ind_j_r].global_route_mark==0 and same_x_flag==0:
                               
                            b=0 
                            for t_a in range (max_track): 
                                if obj[i][ind_j_r].track_left_global[t_a] not in global_track   and obj[i][ind_j_r].global_route_mark==0 :
                                    
                                    global_track.append(obj[i][ind_j_r].track_left_global[t_a])
                                    obj_channel[obj[i][ind_j_r].x_coordinate].track_left.append(obj[i][ind_j_r].track_right_global[t_a])                                    
                                    Global_detailed_routing_main.Global_route_performed(obj, i, j, -1)
                                    Global_detailed_routing_main.Selected_channel(obj, i, j, ind_j_r)                           
                                    for index_c in left_channel_index:
                                        con_j=[]
                                        con_j.append(ind_j_r)
                                        con_j.append(index_c)
                                        obj[i][ind_j_r].connected_pins.append(con_j)
                                        con_index_c=[]
                                        con_index_c.append(index_c)
                                        con_index_c.append(ind_j_r)                                            
                                        obj[i][index_c].connected_pins.append(con_index_c)  
                                        
                                        for k_in in range (len(obj[i])):
                                            br_condition=0
                                            
                                            if obj[i][index_c].identity_n in obj[i][k_in].inter_connect:
                                                if len(obj[i][k_in].inter_connect)!=1  :
                                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                                    for kl in range (len(obj[i])):
                                                        if obj[i][kl].identity_n in obj[i][k_in].inter_connect:
                                                            obj[i][kl].global_route_mark=1
                                                            obj[i][kl].parent_j=k_in
                                                            
                                                            if obj[i][ind_j_r].x_coordinate!=obj[i][kl].x_coordinate:
                                                                obj[i][kl].top_sign=1
                                                                obj[i][kl].bottom_sign=1
                                                            else:
                                                                obj[i][kl].top_sign=-1
                                                                obj[i][kl].bottom_sign=-1                                                                
                                                if len(obj[i][k_in].inter_connect)==1 :
                                                    obj[i][k_in].global_route_mark=1
                                                    obj[i][k_in].parent_j=k_in
                                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                                    if obj[i][ind_j_r].x_coordinate!=obj[i][k_in].x_coordinate:
                                                        obj[i][k_in].top_sign=1
                                                        obj[i][k_in].bottom_sign=1
                                                    else:
                                                        obj[i][k_in].top_sign=-1
                                                        obj[i][k_in].bottom_sign=-1
                                                    br_condition=1
                                            if br_condition==1:    
                                                b=1

                                    if b==1:
                                        break 

                        if cap_count_left<=cap_count_right and obj[i][ind_j_r].global_route_mark==0 and same_x_flag==0:
                            b=0
                            for t_a in range (max_track): 
                                if obj[i][ind_j_r].track_right_global[t_a] not in global_track  and obj[i][ind_j_r].global_route_mark==0 :

                                    global_track.append(obj[i][ind_j_r].track_right_global[t_a])
                                    obj_channel[obj[i][ind_j_r].x_coordinate].track_right.append(obj[i][ind_j_r].track_right_global[t_a])                                    
                                    Global_detailed_routing_main.Global_route_performed(obj, i, j, 1) 
                                    Global_detailed_routing_main.Selected_channel(obj, i, j, ind_j_r) 

                                    for index_c in right_channel_index:                                                
                                        con_j=[]
                                        con_j.append(ind_j_r)
                                        con_j.append(index_c)
                                        obj[i][ind_j_r].connected_pins.append(con_j)
                                        con_index_c=[]
                                        con_index_c.append(index_c)
                                        con_index_c.append(ind_j_r)                                            
                                        obj[i][index_c].connected_pins.append(con_index_c)  
                                                
                                        for k_in in range (len(obj[i])):
                                            br_condition=0
                                            if obj[i][index_c].identity_n in obj[i][k_in].inter_connect:
                                                if len(obj[i][k_in].inter_connect)!=1  :
                                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                                    for kl in range (len(obj[i])):
                                                        if obj[i][kl].identity_n in obj[i][k_in].inter_connect:
                                                            obj[i][kl].global_route_mark=1
                                                            obj[i][kl].parent_j=k_in
                                                            if obj[i][ind_j_r].x_coordinate!=obj[i][kl].x_coordinate:
                                                                obj[i][kl].top_sign=-1
                                                                obj[i][kl].bottom_sign=-1
                                                            else:
                                                                obj[i][kl].top_sign=1
                                                                obj[i][kl].bottom_sign=1                                                                
                                                            
                                                if len(obj[i][k_in].inter_connect)==1 :
                                                    obj[i][k_in].global_route_mark=1
                                                    obj[i][k_in].parent_j=k_in
                                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                                    if obj[i][ind_j_r].x_coordinate!=obj[i][k_in].x_coordinate:
                                                        obj[i][k_in].top_sign=-1
                                                        obj[i][k_in].bottom_sign=-1
                                                    else:
                                                        obj[i][k_in].top_sign=1
                                                        obj[i][k_in].bottom_sign=1
                                                br_condition=1
                                            if br_condition==1:    
                                                b=1                                                    

                                    if b==1:
                                        break 
 
 
 

for i in range (len(obj)):
    for j in range (len(obj[i])):
        if len(obj[i][j].inter_connect)==new_list[i] and obj[i][j].common_track_marked_global==0 and len(obj[i][j].inter_connect)==1 and obj[i][j].global_route_mark==0:                
            obj[i][j].lowest_y_j=j
            flag_track=Global_detailed_routing_main.Track_number_in_channel(obj, row, colomn, global_track, obj[i][j].x_coordinate, obj[i][j].y_coordinate, a4, 0)
            global_track=Global_detailed_routing_main.Global_route_track_selection_unequal(flag_track, obj, i, j, j, global_track, obj_channel)                     

        elif len(obj[i][j].inter_connect)!=0  and obj[i][j].global_route_mark==0 and len(obj[i][j].inter_connect)!=new_list[i] and obj[i][j].common_track_marked_global==0 :
            j_index=j
            
            if len(obj[i][j].inter_connect)!=1 :
                
                xy_list=[]
                for kl in range (len(obj[i])):
                    if obj[i][kl].identity_n in obj[i][j].inter_connect:
                        xxy=[]
                        xxy.append(obj[i][kl].y_coordinate)
                        xxy.append(obj[i][kl].x_coordinate)
                        xy_list.append(xxy)
                xy_list.sort()
                x_value=xy_list[len(xy_list)-1][1]
                y_value=xy_list[len(xy_list)-1][0]

                x_value_h=xy_list[0][1]
                y_value_h=xy_list[0][0]

                for k in range (len(xy_list)):
                    if x_value<a4 and xy_list[k][1]<x_value:
                        x_value=xy_list[k][1]
                    elif x_value>a4 and xy_list[k][1]>x_value:
                        x_value=xy_list[k][1]
                        
                for k in range (len(xy_list)):
                    if x_value_h<a4 and xy_list[k][1]<x_value_h:
                        x_value_h=xy_list[k][1]
                    elif x_value_h>a4 and xy_list[k][1]>x_value_h:
                        x_value_h=xy_list[k][1]                         
                
                (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_value, y_value)
                (i_index, j_index_h)=Global_detailed_routing_main.capacitor_index(obj, x_value_h, y_value_h)
 
                obj[i][j].lowest_y_j=j_index
                obj[i][j].highest_y_j=j_index_h
            if len(obj[i][j].inter_connect)==1: 
                obj[i][j].lowest_y_j=j
                obj[i][j].highest_y_j=j
            
            flag_track=Global_detailed_routing_main.Track_number_in_channel(obj, row, colomn, global_track, obj[i][j_index].x_coordinate, obj[i][j_index].y_coordinate, a4, 0)
            global_track=Global_detailed_routing_main.Global_route_track_selection_unequal(flag_track, obj, i, j,j_index, global_track, obj_channel)


# for k in range (len(same_x_values)):
#     for i in range (len(obj)):
#         for j in range (len(obj[i])):
#             if same_x_values[k][0]==i and same_x_values[k][1]==j : 
                
#                 x_mirror=colomn-obj[i][j].x_coordinate-1
#                 y_mirror=row-obj[i][j].y_coordinate-1
                
#                 (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)
#                 obj[i][j].same_x=1
#                 ind_j_r=same_x_values[k][2]
                
#                 if  i==i_index:
                    
#                     flag_track=0
#                     flag_track=Global_detailed_routing_main.Track_number_in_channel(obj, row, colomn, global_track, obj[i][ind_j_r].x_coordinate, obj[i][ind_j_r].y_coordinate, a4,  1)
#                     global_track=Global_detailed_routing_main.Global_route_track_selection_same_x_unequal(flag_track, obj, i, j, ind_j_r, global_track, obj_channel) 
#                     Global_detailed_routing_main.Selected_channel(obj, i, j, ind_j_r) 
#                     if flag_track==0:
#                         obj[i][ind_j_r].top_sign=1
#                     else:
#                         obj[i][ind_j_r].top_sign=-1

for k in range (len(same_x_values)):
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            if same_x_values[k][0]==i and same_x_values[k][1]==j and obj[i][j].global_route_mark==0: 
                x_mirror=colomn-obj[i][j].x_coordinate-1
                y_mirror=row-obj[i][j].y_coordinate-1
                
                (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)
                obj[i][j].same_x=1
                ind_j_r=same_x_values[k][2]
                
                if obj[i_index][j_index].global_route_mark!=0 and i==i_index:
                    flag_track=0
                    if obj[i_index][j_index].flag_track_j==0:
                        flag_track=1

                    global_track=Global_detailed_routing_main.Global_route_track_selection_same_x_unequal(flag_track, obj, i, j, ind_j_r, global_track, obj_channel) 
                    Global_detailed_routing_main.Selected_channel(obj, i, j, ind_j_r) 
                    if flag_track==0:
                        obj[i][ind_j_r].top_sign=1
                    else:
                        obj[i][ind_j_r].top_sign=-1
                                    
                    for index_c in same_x_values[k][3]:
                        con_j=[]
                        con_j.append(ind_j_r)
                        con_j.append(index_c)
                        obj[i][ind_j_r].connected_pins.append(con_j)
                        con_index_c=[]
                        con_index_c.append(index_c)
                        con_index_c.append(ind_j_r)                                            
                        obj[i][index_c].connected_pins.append(con_index_c)  
                        
                        for k_in in range (len(obj[i])):
                            br_condition=0
                            
                            if obj[i][index_c].identity_n in obj[i][k_in].inter_connect:
                                if len(obj[i][k_in].inter_connect)!=1  :
                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                    for kl in range (len(obj[i])):
                                        if obj[i][kl].identity_n in obj[i][k_in].inter_connect:
                                            obj[i][kl].global_route_mark=1 
                                            obj[i][kl].parent_j=k_in
                                            
                                            
                            if len(obj[i][k_in].inter_connect)==1 :
                                obj[i][k_in].global_route_mark=1
                                obj[i][k_in].parent_j=k_in
        
        
                else:
                    flag_track=Global_detailed_routing_main.Track_number_in_channel(obj, row, colomn, global_track, obj[i][ind_j_r].x_coordinate, obj[i][ind_j_r].y_coordinate, a4,  1)
                    global_track=Global_detailed_routing_main.Global_route_track_selection_same_x_unequal(flag_track, obj, i,j, ind_j_r, global_track, obj_channel) 
                    if flag_track==0:
                        obj[i][ind_j_r].top_sign=1
                    else:
                        obj[i][ind_j_r].top_sign=-1
                        
                    obj[i][j].same_x=1
                    
                    for index_c in same_x_values[k][3]:
                        con_j=[]
                        con_j.append(ind_j_r)
                        con_j.append(index_c)
                        obj[i][ind_j_r].connected_pins.append(con_j)
                        con_index_c=[]
                        con_index_c.append(index_c)
                        con_index_c.append(ind_j_r)                                            
                        obj[i][index_c].connected_pins.append(con_index_c)  
                        
                        for k_in in range (len(obj[i])):
                            br_condition=0
                            
                            if obj[i][index_c].identity_n in obj[i][k_in].inter_connect:
                                if len(obj[i][k_in].inter_connect)!=1  :
                                    Global_detailed_routing_main.Selected_channel(obj, i, k_in, ind_j_r) 
                                    for kl in range (len(obj[i])):
                                        if obj[i][kl].identity_n in obj[i][k_in].inter_connect:
                                            obj[i][kl].global_route_mark=1
                                            obj[i][kl].parent_j=k_in
                                            
                                if len(obj[i][k_in].inter_connect)==1 :
                                    obj[i][k_in].global_route_mark=1
                                    obj[i][k_in].parent_j=k_in 


                                    
                   
seq=0
flag_track=0
Track_num=100
x_coordinate_all=0
for i in range (len(obj)):
    j_index=0
    for j in range (len(obj[i])):
        if obj[i][j].global_route_mark==0 and len(obj[i][j].inter_connect)!=0 and i+1 in All_conn:
            j_index_initial=0
            j_index=j

            y_coor_all_i=[]
            y_coor_all_pos=[]
            for rr_1 in range (len(obj[i])):
                y_coor_all_i.append(obj[i][rr_1].y_coordinate)
            
            
            for rr_1 in range (len(obj[i])):
                if obj[i][rr_1].x_coordinate>a4:
                    y_coor_all_pos.append(obj[i][rr_1].y_coordinate)                
            
            min_y_c=min(y_coor_all_i)
            

            if seq%2==0:
                for rr_1 in range (len(obj[i])):
                    (flag_track_2, Track_num_2)=Global_detailed_routing_main.Track_number_in_channel_2(obj, row, colomn, global_track, i, rr_1, a4)
                    if Track_num>=Track_num_2 and obj[i][j_index].y_coordinate<=obj[i][rr_1].y_coordinate and obj[i][rr_1].y_coordinate!=min_y_c and obj[i][rr_1].y_coordinate==max(y_coor_all_i) and obj[i][rr_1].x_coordinate<a4:                    
                        x_coordinate_all=obj[i][rr_1].x_coordinate 
                        Track_num=Track_num_2
                        flag_track=flag_track_2                        
                        j_index=rr_1 
            else:
                if flag_track==0:
                    flag_track=1
                else:
                    flag_track=0
                Track_num=Track_num 
                x_mirror=colomn-x_coordinate_all-1
                                                                                      
                track_exist=0
                if flag_track==1:
                    track_exist=len(obj_channel[x_mirror].track_left)
                else:
                    track_exist=len(obj_channel[x_mirror].track_right)     
                   
                for rr_1 in range (len(obj[i])):
                    (flag_track_2, Track_num_2)=Global_detailed_routing_main.Track_number_in_channel_2(obj, row, colomn, global_track, i, rr_1, a4)

                    if track_exist==0:
                        if Track_num==Track_num_2 and obj[i][j_index].y_coordinate<=obj[i][rr_1].y_coordinate and obj[i][rr_1].y_coordinate!=min_y_c  and  x_mirror==obj[i][rr_1].x_coordinate :                                            
                            if   obj[i][rr_1].y_coordinate==max(y_coor_all_pos) or obj[i][rr_1].y_coordinate==max(y_coor_all_pos)-1:
                                
                                j_index=rr_1
                                
                                break
                    else:
                        if Track_num>=Track_num_2 and obj[i][j_index].y_coordinate<=obj[i][rr_1].y_coordinate and obj[i][rr_1].y_coordinate!=min_y_c and  obj[i][rr_1].x_coordinate>a4:                    
                            if obj[i][rr_1].y_coordinate==max(y_coor_all_pos) or obj[i][rr_1].y_coordinate==max(y_coor_all_pos)-1 :
                                x_coordinate_all=obj[i][rr_1].x_coordinate 
                                Track_num=Track_num_2
                                flag_track=flag_track_2                        
                                j_index=rr_1                     
                    
            if Track_num==0:
                for k in range (len(obj[i])):
                    obj[i][k].global_route_mark=1
                    obj[i][k].parent_j=j_index
                    
                obj[i][j].lowest_y_j=j_index
                    
                x_value_h=colomn-obj[i][j_index].x_coordinate-1
                y_value_h=row-obj[i][j_index].y_coordinate-1                                    
                    
                (i_index, j_index_h)=Global_detailed_routing_main.capacitor_index(obj, x_value_h, y_value_h) 
                obj[i][j].highest_y_j=j_index_h
                global_track=Global_detailed_routing_main.Global_route_track_selection_same_x_unequal(flag_track, obj, i, j, j_index, global_track, obj_channel)

                if flag_track==0:
                    obj[i][j_index].top_sign=1
                else:
                    obj[i][j_index].top_sign=-1                     
                break 
        
    seq=seq+1  
    if seq%2==0:
        flag_track=0
        Track_num=100 
        
    else:
        flag_track=flag_track
        Track_num=Track_num
        x_coordinate_all=obj[i][j_index].x_coordinate                 
                
                    
                    
            

leftover=[]               
for i in range (len(obj)):
    for j in range (len(obj[i])):
        if obj[i][j].global_route_mark==0 and len(obj[i][j].inter_connect)!=0:
            j_index=j
            if len(obj[i][j].inter_connect)!=1 :
                xy_list=[]
                for kl in range (len(obj[i])):
                    if obj[i][kl].identity_n in obj[i][j].inter_connect:
                        xxy=[]
                        xxy.append(obj[i][kl].y_coordinate)
                        xxy.append(obj[i][kl].x_coordinate)
                        xy_list.append(xxy)
                xy_list.sort()
                x_value=xy_list[len(xy_list)-1][1]
                y_value=xy_list[len(xy_list)-1][0]

                x_value_h=xy_list[0][1]
                y_value_h=xy_list[0][0]                
                         
                
                (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_value, y_value)
                (i_index, j_index_h)=Global_detailed_routing_main.capacitor_index(obj, x_value_h, y_value_h)
 
                obj[i][j].lowest_y_j=j_index
                obj[i][j].highest_y_j=j_index_h

                
            if len(obj[i][j].inter_connect)==1 :
                j_index=j
                obj[i][j].lowest_y_j=j 
                obj[i][j].highest_y_j=j

  
            flag_track=Global_detailed_routing_main.Track_number_in_channel(obj, row, colomn, global_track, obj[i][j_index].x_coordinate, obj[i][j_index].y_coordinate, a4, 0)            
            
            global_track=Global_detailed_routing_main.Global_route_track_selection_unequal(flag_track, obj, i, j, j_index, global_track, obj_channel) 

#Finding out total number of required tracks
global_track.sort()
total_track_count=[]
g_tr=[]
for i in range (colomn):
    track_c=[]
    an_tt=[]
    an_tt.append(i)
    count_t=0
    for j in range (len(obj)):
        for k in range (len(obj[j])):
            if obj[j][k].x_coordinate==i:
                
                for gt in range (len(global_track)):
                    for l in range(len(obj[j][k].track_right_global)):
                        if global_track[gt]==obj[j][k].track_right_global[l] and global_track[gt] not in g_tr:
                            count_t=count_t+1
                            an_tt.append(global_track[gt])
                            g_tr.append(global_track[gt])                
                            break
            if count_t!=0:
                break
        if count_t!=0:
            break    

    total_track_count.append(an_tt)

row_len=[]

for i in range (len(total_track_count)):
    row_len.append(len(total_track_count[i]))

cap.num= max(row_len)

print('cap.num', cap.num)
cap.spacing=Layers_dict['M1']['Space']
cap.wire_width=Layers_dict['M1']['Width']

cap.sx=(cap.num+1)*Layers_dict['M1']['Space'] +(cap.num+1)*Layers_dict['M1']['Width']
cap.sy=(cap.num_h+1)*Layers_dict['M2']['Space']+(cap.num_h+1)*Layers_dict['M2']['Width']
# cap.sx=30
# cap.sy=10

#cap.sx=30

#Calculating the physical coordinates of the unit capacitors
x_coor=[]
y_coor=[]    
detailed_tr=[]
max_x_coor=0
max_y_coor=0
total_bottom_length=0
length_top_1=0

Resistance_before=[]
Resistance_after=[]
capacitance_after=[]
length_last=0

capacitors=[]
length_top=0
horizontal_track_new=[]
horizontal_track_new_top=[]

detailed_tr_top=[]

if space_requirement=="Equal" : 
    
    for i in range (len(obj)): 
        for j in range (len(obj[i])):             
                
            obj[i][j].x_coordinate_new=round(((obj[i][j].x_coordinate+1)-(colomn+1)/2)*(cap.w+cap.sx),5)
            obj[i][j].y_coordinate_new=round(((row+1)/2-(obj[i][j].y_coordinate+1))*(cap.h+cap.sy),5) 
             
    
            obj[i][j].identity.append(round(obj[i][j].x_coordinate_new,5))
            obj[i][j].identity.append(round(obj[i][j].y_coordinate_new,5))
            obj[i][j].identity.append(obj[i][j].cap_name)
    
    
    for i in range (len(obj)): 
        for j in range (len(obj[i])):  
            if obj[i][j].x_coordinate_new not in x_coor:
                x_coor.append(obj[i][j].x_coordinate_new)
            if obj[i][j].y_coordinate_new not in y_coor:
                y_coor.append(obj[i][j].y_coordinate_new) 
    
    max_x_coor=max(x_coor)
    max_y_coor=max(y_coor)
    
    x_coor.sort()
    Via_Num=0
    
    
    close_htrack=[]
    close_track=[]
    
    for i in range (len(obj)): 
        for j in range (len(obj[i])): 
    
            dist_j=0
            fff=0
            if obj[i][j].ratio_marked==1 :
                continue        
    
            obj[i][j].inter_connected.append(obj[i][j].identity)
            stack=[]
            stack_n=[]
            stack_n.append(obj[i][j].identity_n)
            stack.append(obj[i][j].identity)
            p=0
            new_k=j
            while (len(stack_n)!=0):                        
                for q in range (len(obj[i])):
                    if stack_n[p]==obj[i][q].identity_n:
                        new_k=q
                        k_ind=new_k
                for k in range (len(obj[i])):                     
                    d=((stack_n[p][0]-obj[i][k].x_coordinate)**2+(stack_n[p][1]-obj[i][k].y_coordinate)**2)**(1/2)                               
                    
                    if d==1 :
                        if obj[i][k].ratio_marked==0:
    
                            obj[i][k].ratio_marked=1
                            d_1=((stack[p][0]-obj[i][k].x_coordinate_new)**2+(stack[p][1]-obj[i][k].y_coordinate_new)**2)**(1/2)                               
    
                            if stack_n[p][0]==obj[i][k].x_coordinate  :
                                Via_Num=Via_Num+1
    
                                d_1=abs(stack[p][1]-obj[i][k].y_coordinate_new)+cap.spacing
                                obj[i][k].via_number=1
    
                                x_r_n=obj[i][new_k].x_coordinate_new+(cap.w/2)+1*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                                x_l_n=obj[i][new_k].x_coordinate_new-(cap.w/2)-1*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])     

                                x_r_t=obj[i][new_k].x_coordinate_new+(cap.w/2)+1*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                                x_l_t=obj[i][new_k].x_coordinate_new-(cap.w/2)-1*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])     

    
                                htrack=obj[i][new_k].y_coordinate_new-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2
                                htrack_1=obj[i][k].y_coordinate_new-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2
                                
                                htrack_t=obj[i][new_k].y_coordinate_new+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
                                htrack_t_1=obj[i][k].y_coordinate_new+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2                                
    
                                if obj[i][k].x_coordinate_new<=0:
                                    
                                    fl=horizontal(i, round(x_l_n,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new, cap.sx, htrack)
                                    h_t=fl.insert(round(htrack,5))
                                    horizontal_track_new.append(h_t)
    
                                    fl_1=horizontal(i, round(x_l_n,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new, cap.sx, htrack_1)
                                    h_t=fl_1.insert(round(htrack_1,5))
                                    horizontal_track_new.append(h_t)
                                    
                                    fl_t=horizontal(i, round(x_l_t,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new_top, cap.sx, htrack_t)
                                    h_t=fl_t.insert(round(htrack_t,5))
                                    horizontal_track_new_top.append(h_t)
    
                                    fl_t_1=horizontal(i, round(x_l_t,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new_top, cap.sx, htrack_t_1)
                                    h_t=fl_t_1.insert(round(htrack_t_1,5))
                                    horizontal_track_new_top.append(h_t)                                    
                                    
                                elif obj[i][k].x_coordinate_new>0:
    
                                    fl=horizontal(i, round(x_r_n,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new, cap.sx, htrack)
                                    h_t=fl.insert(round(htrack,5))
                                    horizontal_track_new.append(h_t)
    
                                    fl_1=horizontal(i, round(x_r_n,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new, cap.sx, htrack_1)
                                    h_t=fl_1.insert(round(htrack_1,5))
                                    horizontal_track_new.append(h_t)
                                    
                                    fl_t=horizontal(i, round(x_r_t,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new_top, cap.sx, htrack_t)
                                    h_t=fl_t.insert(round(htrack_t,5))
                                    horizontal_track_new_top.append(h_t)
    
                                    fl_t_1=horizontal(i, round(x_r_t,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new_top, cap.sx, htrack_t_1)
                                    h_t=fl_t_1.insert(round(htrack_t_1,5))
                                    horizontal_track_new_top.append(h_t)                                    
                                
                                if cap.first_track_space==0:                    
                                    cap.first_track_space=round(abs(x_r_n-obj[i][j].x_coordinate_new),5)                            
                            if stack_n[p][1]==obj[i][k].y_coordinate :
                                d_1=cap.sx+cap.pin_x
                                
    
                            dist_j=dist_j+d_1
                            stack_n.append(obj[i][k].identity_n)      
                            stack.append(obj[i][k].identity)
                            obj[i][j].inter_connected.append(obj[i][k].identity)
                            
                        obj[i][j].ratio_marked=1                           
                        fff=1
    
                stack_n.pop(0)
                stack.pop(0)
    
            if fff==1:            
                obj[i][j].inter_connect_length=dist_j
    
    
    close_htrack.sort()
    close_track.sort()
    
    
    for i in range (len(obj)): 
        count=0
        flag=0
        for j in range (len(obj[i])):
            if len(obj[i][j].inter_connect)!=1 and len(obj[i][j].inter_connect)!=0:
                count=count+1
                flag=1
                if len(obj[i][j].inter_connect) == new_list[i]:
                    obj[i][j].all_con=1
        if flag==1:
            obj[i][0].counter=count
    
    
    
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            if obj[i][j].inter_connect_length!=0 :
                length_top=length_top+obj[i][j].inter_connect_length
    
    
    for i in range (len(obj)):
        length_for_res=0
        res_a=0
        cap_a=0
        for j in range (len(obj[i])):
            capacitors.append(obj[i][j].identity)
            if len(obj[i][j].inter_connected)!=0 :
                length_for_res=length_for_res+2*obj[i][j].inter_connect_length   
                res_a=res_a+obj[i][j].inter_connect_length*cap.res_per_length
                cap_a=cap_a+obj[i][j].inter_connect_length*cap.cap_per_length_bottom
    
            for c_p in range (1, cap.num+1):
                x_r_n=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                x_l_n=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                    
                obj[i][j].track_right_detailed.append(round(x_r_n,5))        
                
                obj[i][j].track_left_detailed.append(round(x_l_n,5))
    
                if obj[i][j].x_coordinate_new<=0:
                    obj[i][j].track_detailed.append(round(x_l_n,5))
                    obj[i][j].track_detailed.append(round(x_r_n,5))
                   
                elif obj[i][j].x_coordinate_new>0:
                    obj[i][j].track_detailed.append(round(x_r_n,5))
                    obj[i][j].track_detailed.append(round(x_l_n,5))  

                x_r_t=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                x_l_t=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width']) 
                    
                obj[i][j].track_right_detailed_top.append(round(x_r_t,5))        
                
                obj[i][j].track_left_detailed_top.append(round(x_l_t,5))
    
                if obj[i][j].x_coordinate_new<=0:
                    obj[i][j].track_detailed_top.append(round(x_l_t,5))
                    obj[i][j].track_detailed_top.append(round(x_r_t,5))
                   
                elif obj[i][j].x_coordinate_new>0:
                    obj[i][j].track_detailed_top.append(round(x_r_t,5))
                    obj[i][j].track_detailed_top.append(round(x_l_t,5))                      
        

                if c_p==1 and obj[i][j].x_coordinate_new<=0:
                    detailed_tr.append(round(x_l_n,5)) 
                    detailed_tr_top.append(round(x_l_t,5)) 
                if c_p==1 and obj[i][j].x_coordinate_new>0:
                    detailed_tr.append(round(x_r_n,5))   
                    detailed_tr_top.append(round(x_r_t,5))

if space_requirement=="Unequal":
    
    
    for i in range (len(obj)): 
        for j in range (len(obj[i])):             
                
            obj[i][j].new_x=round(((obj[i][j].x_coordinate+1)-(colomn+1)/2)*(cap.w+cap.sx),5)
            obj[i][j].new_y=round(((row+1)/2-(obj[i][j].y_coordinate+1))*(cap.h+cap.sy),5)         
            
            

    plt.savefig('FILTER_equal_channel.png', dpi=300)   
    for i in range (len(obj)): 
        for j in range (len(obj[i])):  
            if obj[i][j].new_x not in x_coor:
                x_coor.append(obj[i][j].new_x)
            if obj[i][j].new_y not in y_coor:
                y_coor.append(obj[i][j].new_y) 
                
    max_x_coor=max(x_coor)
    max_y_coor=max(y_coor)
    
    
    x_uni=set(x_coor)
    x_uni_1=list(x_uni)
    x_uni_1.sort()       
    
    
    new_x_list=[] 
    x_start=0
    x_start_z=0
    
    actual_value=x_uni_1[len(x_uni_1)//2]
    
    if colomn%2==0:
        len_t=len(total_track_count)//2
        sx_mid=(len(total_track_count[len_t-1]))*(Layers_dict['M1']['Space'] +Layers_dict['M1']['Width'])
        
        x_start=((colomn/2+1)-((colomn+1)/2))*(cap.w+sx_mid) 
        x_start_z=((colomn/2)-((colomn+1)/2))*(cap.w+sx_mid)
        
        
        number_track=0
        if len(total_track_count[len_t])>=len(total_track_count[len_t-2]):
            number_track=len(total_track_count[len_t])
        else:
            number_track=len(total_track_count[len_t-2])
        list_a=[]
        
        list_a.append(round(x_start,5))
        list_a.append(round(actual_value,5))    
        list_a.append(len(total_track_count[len_t-1])-1)      
        list_a.append(number_track)   
        
        list_b=[]
        list_b.append(round(x_start_z,5))
        list_b.append(round(-actual_value,5))
        list_b.append(len(total_track_count[len_t-1])-1) 
        list_b.append(number_track) 

        new_x_list.append(list_a)
        new_x_list.append(list_b)
    else:
        x_start=0
        list_b=[]
        list_b.append(round(x_start,5))
        list_b.append(round(x_start,5))
        list_b.append(cap.num)
        list_b.append(cap.num)
        new_x_list.append(list_b)    
    x_zero_ind=0
    for i in range (len(x_uni_1)):
        if x_start==x_uni_1[i]:
            x_zero_ind=i
            
            
    x_val=x_start        
    
    #print('actual value', actual_value)  
    
    
    
    #channel_len_chnl=len(chnl_t)
           
      
    
    new_chnl_t=[]
    for i in range (len(total_track_count)):
        first_n=len(total_track_count[i])
        last_n=len(total_track_count[len(total_track_count)-2-i])
        if first_n>last_n:
            new_chnl_t.append(total_track_count[i])
        elif first_n<last_n:
            new_chnl_t.append(total_track_count[len(total_track_count)-2-i])
        elif first_n==last_n:
            new_chnl_t.append(total_track_count[len(total_track_count)-2-i])    
        

    
    for i in range (len(x_uni_1)//2, len(new_chnl_t)-1):
        x_val = x_val   + (Layers_dict['M1']['Space'] +Layers_dict['M1']['Width'])*(len(new_chnl_t[i])+1)+cap.w
        
        actual_value = actual_value   + cap.sx +cap.w
        
        #print('x_values here', (Layers_dict['M1']['Space'] +Layers_dict['M1']['Width'])*(len(new_chnl_t[i])+2), cap.sx, len(new_chnl_t[i])+1)
        
        list_a=[]
        list_a.append(round(x_val,5))
        list_a.append(round(actual_value,5)) 
        list_a.append(len(new_chnl_t[i])) 
        list_a.append(len(new_chnl_t[i+1])) 
            
        list_b=[]
        list_b.append(-round(x_val,5))
        list_b.append(-round(actual_value,5)) 
        list_b.append(len(new_chnl_t[i]))
        list_b.append(len(new_chnl_t[i+1])) 
        
        new_x_list.append(list_a)
        new_x_list.append(list_b)       
    
    x_coor_n=[]

    for i in range (len(obj)):
        for j in range (len(obj[i])):                    
            if obj[i][j].new_x not in x_coor_n:
                x_coor_n.append(obj[i][j].new_x)
    

        
    device_list_x=[] 
    point_x=[]
    minimum_x_axis_list=[]
    minimum_x_axis_value=0
    
    lsb_name=0
    if circuit_type=='Split':
        msb_name=int(LSB_length)+2
    for i in range (len(obj)):
        var_name=str(i)
        if circuit_type=='Split':
            if obj[i][0].tag=='LSB':
                var_name=str(lsb_name+1)
                lsb_name=lsb_name+1
            if obj[i][0].tag=='MSB' and i==cap.bridge:
                var_name=str(int(LSB_length)+1)
                #msb_name=msb_name+1             
            if obj[i][0].tag=='MSB' and i!=cap.bridge:
                var_name=str(msb_name)
                msb_name=msb_name+1    
    
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            for k in range (len(new_x_list)):
                ind=obj[i][j].cap_name
                color_r= my_color[ind-1] 
                if round(obj[i][j].new_x,5)==round(new_x_list[k][1],5):
                    #print()
                    obj[i][j].x_coordinate_new = new_x_list[k][0]
                    minimum_x_axis_list.append(obj[i][j].x_coordinate_new)
                    obj[i][j].y_coordinate_new = obj[i][j].new_y
                    #obj[i][j].channel_width=new_x_list[k][2]
                    x_l_n=0
                    x_r_n=0
                    x_l_t=0
                    x_r_t=0                
                    if obj[i][j].new_x>0:
                        obj[i][j].channel_width_l=new_x_list[k][2]
                        obj[i][j].channel_width_r=new_x_list[k][3]
                        for c_p in range (1, new_x_list[k][3]+1):
                            x_r_n=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])                        
                            x_r_t=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                            obj[i][j].track_detailed.append(round(x_r_n,5))
                            obj[i][j].track_detailed_top.append(round(x_r_t,5))
                            obj[i][j].track_right_detailed.append(round(x_r_n,5))                  
                            obj[i][j].track_right_detailed_top.append(round(x_r_t,5))
                            
                            if c_p==1:
                                detailed_tr.append(round(x_r_n,5))                         
                
                        for c_p in range (1, new_x_list[k][2]+1):
                            x_l_n=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                            x_l_t=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])      
                            obj[i][j].track_detailed.append(round(x_l_n,5))
                            obj[i][j].track_detailed_top.append(round(x_l_t,5))
                            obj[i][j].track_left_detailed.append(round(x_l_n,5))
                            obj[i][j].track_left_detailed_top.append(round(x_l_t,5)) 
    
                    elif obj[i][j].new_x<0:
                        obj[i][j].channel_width_l=new_x_list[k][3]
                        obj[i][j].channel_width_r=new_x_list[k][2]
                        
                        for c_p in range (1, new_x_list[k][2]+1):
                            x_r_n=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                            x_r_t=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                            obj[i][j].track_detailed.append(round(x_r_n,5))
                            obj[i][j].track_detailed_top.append(round(x_r_t,5))
                            obj[i][j].track_right_detailed.append(round(x_r_n,5))
                            obj[i][j].track_right_detailed_top.append(round(x_r_t,5))                      
    

                        for c_p in range (1, new_x_list[k][3]+1):
                            x_l_n=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                            x_l_t=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])      
                            obj[i][j].track_detailed.append(round(x_l_n,5))
                            obj[i][j].track_detailed_top.append(round(x_l_t,5))
                            obj[i][j].track_left_detailed.append(round(x_l_n,5))
                            obj[i][j].track_left_detailed_top.append(round(x_l_t,5))
    
                            if c_p==1:
                                detailed_tr.append(round(x_l_n,5))

                            
                    elif obj[i][j].new_x==0:
                        obj[i][j].channel_width_l=new_x_list[k][3]
                        obj[i][j].channel_width_r=new_x_list[k][2]
                        for c_p in range (1, new_x_list[k][2]+1):
                            x_r_n=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                            x_r_t=obj[i][j].x_coordinate_new+(cap.w/2)+c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                            obj[i][j].track_detailed.append(round(x_r_n,5))
                            obj[i][j].track_detailed_top.append(round(x_r_t,5))
                            obj[i][j].track_right_detailed.append(round(x_r_n,5))
                            obj[i][j].track_right_detailed_top.append(round(x_r_t,5))
                      
                
                        for c_p in range (1, new_x_list[k][3]+1):
                            x_l_n=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                            x_l_t=obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])      
                            obj[i][j].track_detailed.append(round(x_l_n,5))
                            obj[i][j].track_detailed_top.append(round(x_l_t,5))
                            obj[i][j].track_left_detailed.append(round(x_l_n,5))
                            obj[i][j].track_left_detailed_top.append(round(x_l_t,5))
                            
                            if c_p==1:
                                detailed_tr.append(round(x_l_n,5))                        
    
     
                            
                    obj[i][j].identity_new.append(round(obj[i][j].x_coordinate_new,5))
                    obj[i][j].identity_new.append(round(obj[i][j].y_coordinate_new,5))
                    obj[i][j].identity_new.append(obj[i][j].cap_name)
                    

                    
                    color_num='k'
                    var=str(i+1)
                    xk=obj[i][j].x_coordinate_new
                    yk=obj[i][j].y_coordinate_new

                    diff=(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])*new_x_list[k][2]
                    plt.text(xk-diff/4, yk-(cap.sx/5), var, fontsize=8, color=color_num, fontweight='bold')
                    
                    x1=obj[i][j].x_coordinate_new-cap.w/2
                    y1=obj[i][j].new_y+cap.h/2
                    x2=obj[i][j].x_coordinate_new +cap.w/2    #top plate
                    y2=obj[i][j].new_y+cap.h/2
                    plt.plot([x1,x2],[y1,y2], color=color_r, linewidth=cap.line_w) 
                    
                    x3=obj[i][j].x_coordinate_new-cap.w/2
                    y3=obj[i][j].new_y-cap.h/2
                    x4=obj[i][j].x_coordinate_new +cap.w/2      #bottom plate
                    y4=obj[i][j].new_y-cap.h/2
                    plt.plot([x3,x4],[y3,y4], color=color_r, linewidth=cap.line_w)
                    
                    x1_1=obj[i][j].x_coordinate_new-cap.w/2
                    y1_1=obj[i][j].new_y+cap.h/2
                    x2_1=obj[i][j].x_coordinate_new-cap.w/2   #top plate
                    y2_1=obj[i][j].new_y-cap.h/2
                    plt.plot([x1_1,x2_1],[y1_1,y2_1], color=color_r, linewidth=cap.line_w) 
                    
                    x3_1=obj[i][j].x_coordinate_new +cap.w/2  
                    y3_1=obj[i][j].new_y+cap.h/2
                    x4_1=obj[i][j].x_coordinate_new +cap.w/2      #bottom plate
                    y4_1=obj[i][j].new_y-cap.h/2
                    plt.plot([x3_1,x4_1],[y3_1,y4_1], color=color_r, linewidth=cap.line_w)
                    
                    point_property_1=[]
                    device_list_x.append(obj[i][j].cap_name)
                    point_property_1.append(round(obj[i][j].x_coordinate_new,5))
                    point_property_1.append(round(obj[i][j].new_y,5))
                    point_property_1.append(obj[i][j].cap_name)
                    point_x.append(point_property_1)

    minimum_x_all_new=[]
    minimum_x_all_value_new=0
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            minimum_x_all_new.append(obj[i][j].x_coordinate_new)
    minimum_x_all_value_new=min(minimum_x_all_new)
    
    eq_x=[]
    
    for i in range(len(device_unique_1)):
        same_device_point_1=[]
        for j in range (len(point_x)):
            if (point_x[j][2]==device_unique_1[i]):
                same_device_point_1.append(point_x[j])
        eq_x.append(same_device_point_1)

    
    for i in range (len(obj)): 
        for j in range (len(obj[i])):                         
    
            obj[i][j].identity.append(round(obj[i][j].x_coordinate_new,5))
            obj[i][j].identity.append(round(obj[i][j].y_coordinate_new,5))
            obj[i][j].identity.append(obj[i][j].cap_name)            
    
    
    horizontal_track_new=[]
    horizontal_track_new_top=[]
    close_track=[]
    for i in range (len(obj)): 
        for j in range (len(obj[i])): 
    
            dist_j=0
            fff=0
            if obj[i][j].ratio_marked==1 :
                continue        
    
            obj[i][j].inter_connected.append(obj[i][j].identity)
            stack=[]
            stack_n=[]
            stack_n.append(obj[i][j].identity_n)
            stack.append(obj[i][j].identity)
            p=0
            new_k=j
            while (len(stack_n)!=0):                        
                for q in range (len(obj[i])):
                    if stack_n[p]==obj[i][q].identity_n:
                        new_k=q
                        k_ind=new_k
                for k in range (len(obj[i])):                     
                    d=((stack_n[p][0]-obj[i][k].x_coordinate)**2+(stack_n[p][1]-obj[i][k].y_coordinate)**2)**(1/2)                               
                    
                    if d==1 :
                        if obj[i][k].ratio_marked==0:
    
                            obj[i][k].ratio_marked=1
                            d_1=((stack[p][0]-obj[i][k].x_coordinate_new)**2+(stack[p][1]-obj[i][k].y_coordinate_new)**2)**(1/2)                               
    
                            if stack_n[p][0]==obj[i][k].x_coordinate  :
                                #d_1=cap.sy 
                                d_1=abs(stack[p][1]-obj[i][k].y_coordinate_new)+cap.spacing
                            #if c_p==1: obj[i][j].x_coordinate_new-(cap.w/2)-c_p*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']) 
                                x_r_n=obj[i][new_k].x_coordinate_new+(cap.w/2)+1*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                                x_l_n=obj[i][new_k].x_coordinate_new-(cap.w/2)-1*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])     
    
                                htrack=obj[i][new_k].y_coordinate_new-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2
                                htrack_1=obj[i][k].y_coordinate_new-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2

                                x_r_t=obj[i][new_k].x_coordinate_new+(cap.w/2)+1*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                                x_l_t=obj[i][new_k].x_coordinate_new-(cap.w/2)-1*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])     
    
                                htrack_t=obj[i][new_k].y_coordinate_new+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
                                htrack_t_1=obj[i][k].y_coordinate_new+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
    
                                if obj[i][k].x_coordinate_new<=0:
                                    
                                    track_number=obj[i][new_k].channel_width_l
                                    sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                                    
                                    fl=horizontal(i, round(x_l_n,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new, sx_channel, htrack)
                                    h_t=fl.insert(round(htrack,5))
                                    horizontal_track_new.append(h_t)
                                    
                                    track_number_1=obj[i][k].channel_width_l
                                    sx_channel_1=(track_number_1+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])                                
    
                                    fl_1=horizontal(i, round(x_l_n,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new, sx_channel_1, htrack_1)
                                    h_t=fl_1.insert(round(htrack_1,5))
                                    horizontal_track_new.append(h_t)
                                    
                                    track_number=obj[i][new_k].channel_width_l
                                    sx_channel=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                                    
                                    fl_t=horizontal(i, round(x_l_t,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new_top, sx_channel, htrack_t)
                                    h_t=fl_t.insert(round(htrack_t,5))
                                    horizontal_track_new_top.append(h_t)
                                    
                                    track_number_1=obj[i][k].channel_width_l
                                    sx_channel_1=(track_number_1+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])                                
    
                                    fl_t_1=horizontal(i, round(x_l_t,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new_top, sx_channel_1, htrack_t_1)
                                    h_t=fl_t_1.insert(round(htrack_t_1,5))
                                    horizontal_track_new_top.append(h_t)                                    
                                    
                                elif obj[i][k].x_coordinate_new>0:

                                    track_number=obj[i][new_k].channel_width_r
                                    sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                                    
                                    fl=horizontal(i, round(x_r_n,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new, sx_channel, htrack)
                                    h_t=fl.insert(round(htrack,5))
                                    horizontal_track_new.append(h_t)
    
                                    track_number_1=obj[i][k].channel_width_l
                                    sx_channel_1=(track_number_1+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])                                
    
    
                                    fl_1=horizontal(i, round(x_r_n,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new, sx_channel_1, htrack_1)
                                    h_t=fl_1.insert(round(htrack_1,5))
                                    horizontal_track_new.append(h_t)

                                    track_number=obj[i][new_k].channel_width_r
                                    sx_channel=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                                    
                                    fl_t=horizontal(i, round(x_r_t,5), obj[i][new_k].y_coordinate_new, obj[i][new_k].x_coordinate_new, horizontal_track_new_top, sx_channel, htrack_t)
                                    h_t=fl_t.insert(round(htrack_t,5))
                                    horizontal_track_new_top.append(h_t)
    
                                    track_number_1=obj[i][k].channel_width_l
                                    sx_channel_1=(track_number_1+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])                                
    
    
                                    fl_t_1=horizontal(i, round(x_r_t,5), obj[i][k].y_coordinate_new, obj[i][k].x_coordinate_new, horizontal_track_new_top, sx_channel_1, htrack_t_1)
                                    h_t=fl_t_1.insert(round(htrack_t_1,5))
                                    horizontal_track_new_top.append(h_t)                                    
                                    
                                    
                            if stack_n[p][1]==obj[i][k].y_coordinate :
                                d_1=cap.sx
                                    
                            dist_j=dist_j+d_1
                            stack_n.append(obj[i][k].identity_n)      
                            stack.append(obj[i][k].identity)
                            obj[i][j].inter_connected.append(obj[i][k].identity)
                            
                        obj[i][j].ratio_marked=1                           
                        fff=1
    
                stack_n.pop(0)
                stack.pop(0)
    
            if fff==1:            
                obj[i][j].inter_connect_length=dist_j
    
    
#Connecting the interconnected capacitor groups    
# removed_top_wire=Layout_top_bottom_one_side_1.Generalized_plot_top_bottom_NON_DAC(obj, new_list, Device_Name, mat, row, colomn, cap.w, cap.sx, cap.h, cap.sy, my_color, cap.line_w_2, color_mat, cap.metal_layer_number, cap.wire_width, cap.spacing, Terminal_list, Layers_dict, cap)
removed_top_wire=Layout_top_bottom_one_side_1.Generalized_plot_top_bottom_3(obj, new_list, Device_Name, mat, row, colomn, cap.w, cap.sx, cap.h, cap.sy, my_color, cap.line_w_2, color_mat, cap.metal_layer_number, cap.wire_width, cap.spacing, Terminal_list, Layers_dict, cap)


y_coor_l=[]      
  
for i in range (len(obj)):
    for j in range (len(obj[i])):
        if obj[i][j].y_coordinate_new not in y_coor_l:            
            cap.max_y.append(obj[i][j].y_coordinate_new)
            y_coor_l.append(obj[i][j].y_coordinate_new)

    
x_coor_l=[]

for i in range (len(obj)):
    for j in range (len(obj[i])):                    
        if obj[i][j].x_coordinate_new not in x_coor_l:
            x_coor_l.append(obj[i][j].x_coordinate_new)


maximum_y=max(cap.max_y)
minimum_y=min(cap.max_y)

wire_length_LSB=0
wire_length_MSB=0
if circuit_type=='Binary': 
    (length_top_1, total_bottom_length)=Layout_top_bottom_one_side_1.Top_plate_routing_plot(obj,  mat, row, colomn, cap.w, cap.sx, cap.h, cap.sy, my_color, cap.line_w, a4,  cap.spacing, cap.wire_width, Terminal_list, Layers_dict, cap)
elif circuit_type=='Split': 
    (wire_length_LSB, wire_length_MSB)=Layout_top_bottom_one_side_1.Top_plate_routing_plot_Split_DAC(obj,  mat, row, colomn, cap.w, cap.sx, cap.h, cap.sy, my_color, cap.line_w, a4,  cap.spacing, cap.wire_width, Terminal_list, Layers_dict, cap, detailed_tr_top, horizontal, horizontal_track_new_top, maximum_y)

if circuit_type=='Split':
    kk=0
    flag=0
    flag_1=0
    if obj[cap.bridge][0].y_coordinate!=row-1:
        (i_index_4, j_index_4)=Global_detailed_routing_main.capacitor_index(obj, obj[cap.bridge][0].x_coordinate, obj[cap.bridge][0].y_coordinate+1)
        if i_index_4%2==0 and flag_1==0 and i_index_4!=cap.bridge:            
            x=obj[cap.bridge][0].x_coordinate_new
            flag_1=1
            y1=obj[cap.bridge][0].y_coordinate_new-cap.h/2 + cap.pin_y
            y2=obj[i_index_4][j_index_4].y_coordinate_new+cap.h/2 - cap.pin_y
            y=y2            

            plt.gca().add_patch(patches.Rectangle((x-Layers_dict['M3']['Width']/2, y-Layers_dict['V2']['VencA_H']-Layers_dict['V2']['WidthY']/2),  Layers_dict['M3']['Width'], abs(y1-y2)+2*Layers_dict['V2']['VencA_H']+Layers_dict['V2']['WidthY'],color='k'))                                                                        
            wire_segment_1=Layout_top_bottom_one_side_1.wire('M3', None, Layers_dict['M3']['Direction'])
            Terminal_list.append(wire_segment_1.segment(x-Layers_dict['M3']['Width']/2, y-Layers_dict['V2']['VencA_H']-Layers_dict['V2']['WidthY']/2, x+Layers_dict['M3']['Width']/2, y+abs(y1-y2)+Layers_dict['V2']['VencA_H']+Layers_dict['V2']['WidthY']/2, 'drawing', Layers_dict['M3']['Color'][0]))


    if obj[cap.bridge][1].y_coordinate!=row-1:         
        (i_index_4, j_index_4)=Global_detailed_routing_main.capacitor_index(obj, obj[cap.bridge][1].x_coordinate, obj[cap.bridge][1].y_coordinate+1) 

        if i_index_4%2==0 and flag_1==0 and i_index_4!=cap.bridge:            
            x=obj[cap.bridge][1].x_coordinate_new
            flag_1=1
            y1=obj[cap.bridge][1].y_coordinate_new-cap.h/2 + cap.pin_y
            y2=obj[i_index_4][j_index_4].y_coordinate_new+cap.h/2 - cap.pin_y
            y=y2            

            plt.gca().add_patch(patches.Rectangle((x-Layers_dict['M3']['Width']/2, y-Layers_dict['V2']['VencA_H']-Layers_dict['V2']['WidthY']/2),  Layers_dict['M3']['Width'], abs(y1-y2)+2*Layers_dict['V2']['VencA_H']+Layers_dict['V2']['WidthY'],color='k'))                                                                        
            wire_segment_1=Layout_top_bottom_one_side_1.wire('M3', None, Layers_dict['M3']['Direction'])
            Terminal_list.append(wire_segment_1.segment(x-Layers_dict['M3']['Width']/2, y-Layers_dict['V2']['VencA_H']-Layers_dict['V2']['WidthY']/2, x+Layers_dict['M3']['Width']/2, y+abs(y1-y2)+Layers_dict['V2']['VencA_H']+Layers_dict['V2']['WidthY']/2, 'drawing', Layers_dict['M3']['Color'][0]))

    if obj[cap.bridge][0].y_coordinate!=0 :
        (i_index_3, j_index_3)=Global_detailed_routing_main.capacitor_index(obj, obj[cap.bridge][0].x_coordinate, obj[cap.bridge][0].y_coordinate-1)          
        if i_index_3%2==0 and flag_1==0 and i_index_3!=cap.bridge:            
            x=0

            y1=obj[cap.bridge][0].y_coordinate_new-cap.h/2 + cap.pin_y+Layers_dict['M2']['Width']/2
            y2=obj[i_index_3][j_index_3].y_coordinate_new+cap.h/2 - cap.pin_y-Layers_dict['M2']['Width']/2
            y=y1 
            flag_1=1
            obj[cap.bridge][0].via_number_top=obj[cap.bridge][0].via_number_top+1
            

            if  obj[cap.bridge][0].x_coordinate_new<=0:           
                x=obj[cap.bridge][0].x_coordinate_new-cap.w/2-Layers_dict['M3']['Space']-Layers_dict['M3']['Width']
                Layout_top_bottom_one_side_1.top_plate_vertical(x, y, y1, y2, Layers_dict, Terminal_list, cap)
    
                Layout_top_bottom_one_side_1.left_array_top_plate_horizontal(x, y1, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y1, cap.h, Layers_dict, Terminal_list, cap)
                
                Layout_top_bottom_one_side_1.left_array_top_plate_horizontal(x, y2, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y2, cap.h, Layers_dict, Terminal_list, cap)
            elif  obj[cap.bridge][0].x_coordinate_new>0: 
                x=obj[cap.bridge][0].x_coordinate_new+cap.w/2+Layers_dict['M3']['Space']+Layers_dict['M3']['Width']
                Layout_top_bottom_one_side_1.top_plate_vertical(x, y, y1, y2, Layers_dict, Terminal_list, cap)
 
                Layout_top_bottom_one_side_1.right_array_top_plate_horizontal(x, y1, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y1, cap.h, Layers_dict, Terminal_list, cap) 
                            
                Layout_top_bottom_one_side_1.right_array_top_plate_horizontal(x, y2, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y2, cap.h, Layers_dict, Terminal_list, cap)                 


    if  obj[cap.bridge][1].y_coordinate!=0:
        (i_index_3, j_index_3)=Global_detailed_routing_main.capacitor_index(obj, obj[5][1].x_coordinate, obj[5][1].y_coordinate-1)                  
        if i_index_3%2==0 and flag_1==0 and i_index_3!=cap.bridge:             
            x=0

            y1=obj[cap.bridge][1].y_coordinate_new-cap.h/2 + cap.pin_y+Layers_dict['M2']['Width']/2
            y2=obj[i_index_3][j_index_3].y_coordinate_new+cap.h/2 - cap.pin_y-Layers_dict['M2']['Width']/2
            y=y1 
            flag_1=1
            obj[cap.bridge][0].via_number_top=obj[cap.bridge][0].via_number_top+1

            if  obj[cap.bridge][1].x_coordinate_new<=0:           
                x=obj[cap.bridge][1].x_coordinate_new-cap.w/2-Layers_dict['M3']['Space']-Layers_dict['M3']['Width']
                Layout_top_bottom_one_side_1.top_plate_vertical(x, y, y1, y2, Layers_dict, Terminal_list, cap)
    
                Layout_top_bottom_one_side_1.left_array_top_plate_horizontal(x, y1, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y1, cap.h, Layers_dict, Terminal_list, cap)
                
                Layout_top_bottom_one_side_1.left_array_top_plate_horizontal(x, y2, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y2, cap.h, Layers_dict, Terminal_list, cap)
            elif  obj[cap.bridge][1].x_coordinate_new>0: 
                x=obj[cap.bridge][1].x_coordinate_new+cap.w/2+Layers_dict['M3']['Space']+Layers_dict['M3']['Width']
                Layout_top_bottom_one_side_1.top_plate_vertical(x, y, y1, y2, Layers_dict, Terminal_list, cap)
 
                Layout_top_bottom_one_side_1.right_array_top_plate_horizontal(x, y1, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y1, cap.h, Layers_dict, Terminal_list, cap) 
                            
                Layout_top_bottom_one_side_1.right_array_top_plate_horizontal(x, y2, Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.top_plate_via(x, y2, cap.h, Layers_dict, Terminal_list, cap)                 

length_top=0
ctb_list=[]
for i in range (len(obj)): 
    ctb_per_cap=0
    for j in range (len(obj[i])):
        if len(obj[i][j].inter_connected)!=0:
            ctb_per_cap=ctb_per_cap+obj[i][j].inter_connect_length*cap.cap_per_length_tb

        if i%2==0 and i!=cap.bridge:
            wire_length_LSB=wire_length_LSB+obj[i][j].inter_connect_length

        elif i%2!=0 and i!=cap.bridge:
            wire_length_MSB=wire_length_MSB+obj[i][j].inter_connect_length
    
    ctb_list.append(ctb_per_cap)


for i in range (len(obj)): 
    count=0
    flag=0
    for j in range (len(obj[i])):
        if len(obj[i][j].inter_connect)!=1 and len(obj[i][j].inter_connect)!=0:
            count=count+1
            flag=1
            if len(obj[i][j].inter_connect) == new_list[i]:
                obj[i][j].all_con=1
    if flag==1:
        obj[i][0].counter=count

      


wire_length_bottom=[]
wire_length_top=[]

Via_Num=0
width=cap.w+cap.sx
tracks=[]

delay_list=[]
bridge_cap_bottom=0
bridge_cap_top=0

#Performing detailed routing 

for i in range (len(obj)):
    flag=0
    index=0
    for j in range (len(obj[i])):
        ind=obj[i][j].cap_name
        color_r= my_color[ind-1]
        if len(obj[i][j].inter_connected)!=0 and obj[i][j].detailed_route_mark==0  and i+1 not in cap.ring_name_cap :
            if obj[i][j].common_track_marked_global==0: 
                track_one=0 
                track_two=0 
                
                j_index=0

                x_mirror=colomn-obj[i][obj[i][j].lowest_y_j].x_coordinate-1
                y_mirror=row-obj[i][obj[i][j].lowest_y_j].y_coordinate-1
                
                (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)

                track_number=0
                
                
                track_number=cap.num
                
                if obj[i_index][j_index].detailed_route_mark!=0 and i==i_index: 
                    track_one=-obj[i][j_index].final_track_bottom
                    detailed_tr.append(track_one)
                    track_two=-obj[i][j_index].final_track_top
                    if obj[i][j].top_sign>=0:
                        if space_requirement=='Unequal':
                            track_number=obj[i][obj[i][j].lowest_y_j].channel_width_r
                        for k in range (len(obj[i][obj[i][j].lowest_y_j].track_right_detailed)):
                            if round(obj[i][obj[i][j].lowest_y_j].track_right_detailed[k],5)==round(track_one,5):
                                index=k
                                break
                    else:
                        if space_requirement=='Unequal':
                            track_number=obj[i][obj[i][j].lowest_y_j].channel_width_l
                        for k in range (len(obj[i][obj[i][j].lowest_y_j].track_left_detailed)):
                            if round(obj[i][obj[i][j].lowest_y_j].track_left_detailed[k],5)==round(track_one,5):
                                index=k
                                break                        
                else:                                                            
                    if obj[i][j].top_sign>=0:
                        if space_requirement=='Unequal':
                            track_number=obj[i][obj[i][j].lowest_y_j].channel_width_r
                        (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][obj[i][j].lowest_y_j].track_right_detailed, detailed_tr)
                        if obj[i][j].cap_name not in All_conn:
                            track_two=obj[i][obj[i][j].highest_y_j].track_right_detailed_top[index]
                        else:
                            track_two=obj[i][obj[i][j].highest_y_j].track_left_detailed_top[index]
                    else:
                        if space_requirement=='Unequal':
                            track_number=obj[i][obj[i][j].lowest_y_j].channel_width_l
                        (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][obj[i][j].lowest_y_j].track_left_detailed, detailed_tr)
                        if obj[i][j].cap_name not in All_conn:
                            track_two=obj[i][obj[i][j].highest_y_j].track_left_detailed_top[index]
                        else:
                            track_two=obj[i][obj[i][j].highest_y_j].track_right_detailed_top[index]
                        
                    
                tracks.append(track_one)
                x_value_j=obj[i][obj[i][j].lowest_y_j].x_coordinate_new
                y_value_j=obj[i][obj[i][j].lowest_y_j].y_coordinate_new
                new_assign=[]
                new_assign.append(round(track_one,5))
                htrack=y_value_j-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2
                
                sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                
                fl=horizontal(i, track_one, y_value_j, x_value_j, horizontal_track_new, sx_channel, htrack)
                    
                new_f=fl.horizontal_routing()
    
                if new_f==1:                    
                    htrack=fl.horizontal_track_assign()
                    cap.a_t_h_ratio.append(round(htrack,5))
                
                new_assign.append(round(htrack,5))                                   
                h_t=fl.insert(round(htrack,5))
                horizontal_track_new.append(h_t)                
                Via_Num=Via_Num+1 

                #htrack_l=(minimum_y-((cap.h)/2)-(cap.sy/(cap.num_h)))                                                       
                # htrack_l=(minimum_y-((cap.h)/2)-Layers_dict['M2']['Width']/2-Layers_dict['M2']['Space'])
                htrack_l=(minimum_y-((cap.h)/2)-Layers_dict['M2']['Width']/2-Layers_dict['M2']['Space'])
                
                
                wire_2=abs(x_value_j-track_one)-(cap.w/2) +obj[i][j].inter_connect_length
                
                new_assign.append(obj[i][j].cap_name)
                                       
                n_w=[]
                n_w.append(wire_2)
                n_w.append(new_assign)
                n_w.append(index)
                cap.wire_length.append(n_w)
                wire_length_bottom.append(n_w)  
                    
                htrack_u=(maximum_y+((cap.h)/2)+(cap.sy/(cap.num_h)))
                Global_detailed_routing_main.Detailed_route_performed(obj, i, j)
                Layout_top_bottom_one_side_1.Horizontal_track_plot(track_one, htrack, cap.w, cap.h, x_value_j, y_value_j, cap.line_w, color_r, new_f, Layers_dict, Terminal_list, cap)
                obj[i][j].via_number=1

                #(x_top, y_top)=Global_detailed_routing_main.xy_value_top(track_two, obj[i][j].inter_connected, cap.w)  
                if circuit_type=='General':
                    x_top=obj[i][obj[i][j].highest_y_j].x_coordinate_new
                    y_top=obj[i][obj[i][j].highest_y_j].y_coordinate_new
                    new_assign_top=[]
                    new_assign_top.append(round(track_two,5))
                    htrack_top=y_top+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
                    
                    sx_channel_top=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                    fl_top=horizontal(i, track_one, y_top, x_top, horizontal_track_new_top, sx_channel_top, htrack_top)
                        
                    new_f_top=fl_top.horizontal_routing_top()
                    
                    obj[i][j].via_number_top=1
        
                    if new_f_top==1:                    
                        htrack_top=fl_top.horizontal_track_assign_top()
                        cap.a_t_h_ratio.append(round(htrack_top,5))
                    
                    new_assign_top.append(round(htrack_top,5))                                   
                    h_t=fl_top.insert(round(htrack_top,5))
                    horizontal_track_new_top.append(h_t)                
                    Via_Num=Via_Num+1 
    
                    #htrack_l=(minimum_y+((cap.h)/2)+(cap.sy/(cap.num_h)))                                                       
                    
                    wire_2=abs(x_top-track_two)-(cap.w/2) +obj[i][j].inter_connect_length
                    
                    new_assign_top.append(obj[i][j].cap_name)
                                           
                    n_w_top=[]
                    n_w_top.append(wire_2)
                    n_w_top.append(new_assign_top)
                    n_w_top.append(index)
                    cap.wire_length_top.append(n_w_top)
                    wire_length_top.append(n_w_top)  
                        
                    htrack_u=(maximum_y+((cap.h)/2)+(cap.sy/(cap.num_h)))
                    Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_two, htrack_top, cap.w, cap.h, x_top, y_top, cap.line_w, color_r, new_f_top, Layers_dict, Terminal_list, cap)

                Global_detailed_routing_main.track_assignment(obj, i, j, track_one, track_two)


                                
        if len(obj[i][j].inter_connected)!=0 and obj[i][j].detailed_route_mark==0 and obj[i][j].common_track_marked_global==1 and i+1 not in cap.ring_name_cap:                                        
            for j_new in range (len(obj[i])):                
                flag_j=0                    
                if obj[i][j_new].identity in obj[i][j].inter_connected: 
                    new_assign=[]
                    wire_2_2=0                        
                         
                    if len(obj[i][j_new].connected_pins)!=0:
                        #print('obj[i][j].inter_connected', i,  obj[i][j].inter_connected)
                        
                        delay_back=0
                        ind_j=obj[i][j_new].connected_pins[0][0]
                        other_index=[]
                        for k_1 in range (len(obj[i][j_new].connected_pins)):
                            other_index.append(obj[i][j_new].connected_pins[k_1][1])


                        tr_ind=other_index[0]
                        for k_2 in range (len(other_index)):
                            if abs(obj[i][j_new].x_coordinate-obj[i][other_index[k_2]].x_coordinate)==1:
                                tr_ind=other_index[k_2]
                                break

                        track_one=0
                        track_top=0

                        x_mirror=colomn-obj[i][j].x_coordinate-1
                        y_mirror=row-obj[i][j].y_coordinate-1
                        
                        (i_index, j_index)=Global_detailed_routing_main.capacitor_index(obj, x_mirror, y_mirror)
        
                        if obj[i_index][j_index].detailed_route_mark!=0 and i==i_index: 
                            track_one=-obj[i_index][j_index].final_track_bottom
                            detailed_tr.append(track_one)
                            track_top=-obj[i_index][j_index].final_track_top
                            #if obj[i][j].top_sign>=0:
                            for k in range (len(obj[i][j].track_detailed)):
                                if round(obj[i][j].track_detailed[k],5)==round(track_one,5):
                                    index=k 
                                    break
                        else:
                            if obj[i][j].same_x==1:
                                if obj[i][j].top_sign>=0:
                                    (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][ind_j].track_right_detailed, detailed_tr)
                                    track_top=obj[i][ind_j].track_right_detailed_top[index]
                                else:
                                    (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][ind_j].track_left_detailed, detailed_tr)
                                    track_top=obj[i][ind_j].track_left_detailed_top[index]                                
                            else:
                                for tr in range (len(obj[i][ind_j].track_detailed)):
                                    for tr_1 in range (len(obj[i][tr_ind].track_detailed)):
                                        if obj[i][ind_j].track_detailed[tr]== obj[i][tr_ind].track_detailed[tr_1]  and obj[i][ind_j].track_detailed[tr] not in detailed_tr :
                                            track_one=obj[i][ind_j].track_detailed[tr]
                                            track_top=obj[i][ind_j].track_detailed_top[tr]
                                            detailed_tr.append(round(obj[i][ind_j].track_detailed[tr],5))
                                            
                                            break
                                    if track_one!=0:
                                        break
    
                        tracks.append(track_one)
                                    
                        y_min_cal_j_list=[]
                        y_value_j=obj[i][ind_j].y_coordinate_new 
                        x_value_j=obj[i][ind_j].x_coordinate_new 
                        flag_xx=0    
                        for now in range (len(obj[i][j].inter_connected)):
                            if abs(obj[i][j].inter_connected[now][0]-track_one)<width:
                                y_min_cal_j_list.append(obj[i][j].inter_connected[now][1]) 
                        track_number=cap.num
                        sx_channel=0
                        if space_requirement=='Unequal':
                            if x_value_j<track_one:
                                track_number=obj[i][ind_j].channel_width_r
                                #print('what are the track_number', i, track_number, obj[i][ind_j].x_coordinate,obj[i][ind_j].x_coordinate_new,x_value_j,track_one )
                            else:
                                track_number=obj[i][ind_j].channel_width_l
                                #print('what are the track_number in left', i, track_number, obj[i][ind_j].x_coordinate)
                        
                            sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                        if space_requirement=='Equal':
                            sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
                            
                        
                        
                        new_assign.append(round(track_one,5))
                        htrack=y_value_j-((cap.h)/2) +cap.pin_y+Layers_dict['M2']['Width']/2
                        
                        fl_b=horizontal(i, track_one, y_value_j, x_value_j, horizontal_track_new, sx_channel, htrack)                                            
                        new_f=fl_b.horizontal_routing()
                            
                        if new_f==1:                                
                            htrack=fl_b.horizontal_track_assign()
                            cap.a_t_h_ratio.append(round(htrack,5))
                            
                        new_assign.append(round(htrack,5))

                        h_t=fl_b.insert(round(htrack,5))
                        horizontal_track_new.append(h_t)
                                        
                        wire_2_2=abs(x_value_j-track_one)+obj[i][j].inter_connect_length     -(cap.w/2)                                        
                        #htrack_l=(minimum_y-((cap.h)/2)-(cap.sy/(cap.num_h)))
                        Global_detailed_routing_main.Detailed_route_performed(obj, i, j)           
                        Via_Num=Via_Num+1  
                        obj[i][j].via_number=1                                      

                        Layout_top_bottom_one_side_1.Horizontal_track_plot(track_one, htrack, cap.w, cap.h, x_value_j, y_value_j, cap.line_w, color_r, new_f, Layers_dict, Terminal_list, cap)
  
                        htrack_l=(minimum_y-((cap.h)/2)-Layers_dict['M2']['Width']/2-Layers_dict['M2']['Space']) 
                        
                        #y_value_max=max(y_min_cal_j_list)
                        new_assign_top=[]
                        y_value_max=obj[i][ind_j].y_coordinate_new 
                        if circuit_type=='General':
                            
    
                            new_assign_top.append(round(track_top,5))
                            htrack_top=y_value_max+((cap.h)/2) -cap.pin_y-Layers_dict['M2']['Width']/2
                            
                            sx_channel_top=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                            
                            fl_b_top=horizontal(i, track_top, y_value_max, x_value_j, horizontal_track_new_top, sx_channel_top, htrack_top)                                            
                            new_f_top=fl_b_top.horizontal_routing_top()
                            
                                                        
                            if new_f_top==1:                                
                                htrack_top=fl_b_top.horizontal_track_assign_top()
                                cap.a_t_h_ratio.append(round(htrack_top,5))
                            new_assign_top.append(round(htrack_top,5))
    
                            h_t_top=fl_b_top.insert(round(htrack_top,5))
                            horizontal_track_new_top.append(h_t_top)
                                            
                            wire_2_2=abs(x_value_j-track_top)+obj[i][j].inter_connect_length     -(cap.w/2)                                                                            
    
                            Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_top, htrack_top, cap.w, cap.h, x_value_j, y_value_max, cap.line_w, color_r, new_f_top, Layers_dict, Terminal_list, cap)
    
                            htrack_u=(maximum_y+((cap.h)/2)+(cap.sy/(cap.num_h)))
                        
                        Global_detailed_routing_main.track_assignment(obj, i, j, track_one, track_top)
                        flag_j=1
                        branch_delay=0
                        loop_c=1
                        htrack_bridge=0
                        for index_c in other_index:
                            index_plot=0
                            
                            for j_1 in range (len(obj[i])):
                                if obj[i][index_c].identity in obj[i][j_1].inter_connected: 
                                    index_plot=j_1
                                    break
    
                            if obj[i][index_c].detailed_route_mark==0:                                                      
                                x_value_index_c=obj[i][index_c].x_coordinate_new                                                
                                y_min_cal_index_list=[]
                                for now in range (len(obj[i][index_plot].inter_connected)):
                                    if abs(obj[i][index_plot].inter_connected[now][0]-track_one)<width:
                                        y_min_cal_index_list.append(obj[i][index_plot].inter_connected[now][1])                            

                                #y_min_cal_index_bottom=min(y_min_cal_index_list)    
                                y_min_cal_index_bottom=obj[i][index_c].y_coordinate_new       
                                htrack_index=y_min_cal_index_bottom-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2
                                fl_index_c=horizontal(i, track_one, y_min_cal_index_bottom, x_value_index_c, horizontal_track_new, sx_channel, htrack_index)
                                
                                new_f_index_c=fl_index_c.horizontal_routing()
                                
                                if new_f_index_c==1:
                                    
                                    htrack_index=fl_index_c.horizontal_track_assign()
                                    cap.a_t_h_ratio.append(round(htrack_index,5))
                                    
                                htrack_bridge=htrack_index
                                
                                new_assign.append(round(htrack_index,5))
                                h_t_index_c=fl_index_c.insert(round(htrack_index,5))

                                horizontal_track_new.append(h_t_index_c)

                                Via_Num=Via_Num+2
                                obj[i][index_c].via_number=2               
                                                    
                                wire_2_2=wire_2_2+abs(x_value_index_c-track_one)-(cap.w/2)+obj[i][index_plot].inter_connect_length
                                Global_detailed_routing_main.Detailed_route_performed(obj, i, index_plot)                                
                                Layout_top_bottom_one_side_1.Horizontal_track_plot(track_one, htrack_index, cap.w, cap.h, x_value_index_c, y_min_cal_index_bottom, cap.line_w, color_r, new_f_index_c, Layers_dict, Terminal_list, cap)

                                
                                #y_min_cal_index_top=max(y_min_cal_index_list)
                                if circuit_type=='General':
                                    y_min_cal_index_top=obj[i][index_c].y_coordinate_new       
                                    x_value_index_top=obj[i][index_c].x_coordinate_new      
                                    #(x_value_index_top,y_min_cal_index_top)=Global_detailed_routing_main.xy_value_top(track_top, obj[i][index_plot].inter_connected, cap.w)     
                                    htrack_index_top=y_min_cal_index_top+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
                                    fl_index_c_top=horizontal(i, track_top, y_min_cal_index_top, x_value_index_top, horizontal_track_new_top, sx_channel_top, htrack_index_top)
                                    #print('are u even coming here', i, track_top, y_min_cal_index_top, x_value_index_top, sx_channel_top, htrack_index_top, track_number)
                                    new_f_index_c_top=fl_index_c_top.horizontal_routing_top()
                                    
                                    if new_f_index_c_top==1: 
                                        
                                        htrack_index_top=fl_index_c_top.horizontal_track_assign_top()
                                        cap.a_t_h_ratio.append(round(htrack_index_top,5))
                                    new_assign_top.append(round(htrack_index_top,5))
                                    h_t_index_c_top=fl_index_c_top.insert(round(htrack_index_top,5))
    
                                    horizontal_track_new_top.append(h_t_index_c_top)
                   
                                    wire_2_2=wire_2_2+abs(x_value_index_top-track_top)-(cap.w/2)+obj[i][index_plot].inter_connect_length
                                    #Global_detailed_routing_main.Detailed_route_performed(obj, i, index_plot)                                
                                    Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_top, htrack_index_top, cap.w, cap.h, x_value_index_top, y_min_cal_index_top, cap.line_w, color_r, new_f_index_c_top, Layers_dict, Terminal_list, cap)

                                
                                loop_c=loop_c+1
                                Global_detailed_routing_main.track_assignment(obj, i, index_plot, track_one, track_top)  
                                                      
                        if circuit_type=='Split' and i==cap.bridge: 
                            #print('are u crazy', i)
                            var=str(int(i))
                            Layout_top_bottom_one_side_1.trunk_routing(track_one, htrack_bridge, htrack, Layers_dict, Terminal_list, cap, color_r, index, var)     
                            Layout_top_bottom_one_side_1.trunk_routing_via(track_one, htrack, Layers_dict, Terminal_list, cap)
                            Layout_top_bottom_one_side_1.trunk_routing_via(track_one, htrack_bridge, Layers_dict, Terminal_list, cap)
                            #Layout_top_bottom_one_side_1.top_plate_via(x, y, cap.h, Layers_dict, Terminal_list, cap)
                            bridge_cap_bottom=abs(htrack_bridge-htrack)+abs(obj[i][other_index[0]].x_coordinate_new-track_one)-(cap.w/2)+cap.pin_x+abs(x_value_j-track_one)-(cap.w/2)+cap.pin_x
                            
                            sx_channel_top=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                            
         
                            htrack_top=y_value_j+((cap.h)/2) -cap.pin_y-Layers_dict['M2']['Width']/2

                            fl_b=horizontal(i, track_one, y_value_j, x_value_j, horizontal_track_new, sx_channel_top, htrack)                                            
                            new_f=fl_b.horizontal_routing_top()
                                
                            if new_f==1:                               
                                htrack_top=fl_b.horizontal_track_assign_top()
                                cap.a_t_h_ratio.append(round(htrack,5))

                            htrack_index_top=y_min_cal_index_bottom+((cap.h)/2)-cap.pin_y-Layers_dict['M2']['Width']/2
                            fl_index_c=horizontal(i, track_one, obj[i][other_index[0]].y_coordinate_new, obj[i][other_index[0]].x_coordinate_new, horizontal_track_new, sx_channel_top, htrack_index)
                                
                            new_f_index_c=fl_index_c.horizontal_routing_top()
                            
                            if new_f_index_c==1:                      
                                htrack_index_top=fl_index_c.horizontal_track_assign_top()
                                cap.a_t_h_ratio.append(round(htrack_index,5))

                            obj[i][other_index[0]].via_number_top=obj[i][other_index[0]].via_number_top+1   
                            obj[i][j].via_number_top=obj[i][j].via_number_top+1   
                            
                            bridge_cap_top=abs(htrack_index_top-htrack_top)+abs(obj[i][other_index[0]].x_coordinate_new-track_one)-(cap.w/2)+cap.pin_x+abs(x_value_j-track_one)-(cap.w/2)+cap.pin_x                            

                            Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_top, htrack_top, cap.w, cap.h, x_value_j, y_value_j, cap.line_w, color_r, new_f, Layers_dict, Terminal_list, cap)

                            Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_top, htrack_index_top, cap.w, cap.h, obj[i][other_index[0]].x_coordinate_new, obj[i][other_index[0]].y_coordinate_new   , cap.line_w, color_r, new_f_index_c, Layers_dict, Terminal_list, cap)

                            Layout_top_bottom_one_side_1.trunk_routing_top(track_top, htrack_index_top, htrack_top, Layers_dict, Terminal_list, cap, 'r', var)     
                            Layout_top_bottom_one_side_1.top_plate_via(track_one, htrack_top, cap.h, Layers_dict, Terminal_list, cap)
                            Layout_top_bottom_one_side_1.top_plate_via(track_one, htrack_index_top, cap.h, Layers_dict, Terminal_list, cap)
                                


                        new_assign.append(obj[i][j].cap_name)                                       
                        n_w=[]
                        n_w.append(wire_2_2)
                        n_w.append(new_assign)
                        n_w.append(index)
                        cap.wire_length.append(n_w)
                        wire_length_bottom.append(n_w) 
                        if circuit_type=='General':
                            new_assign_top.append(obj[i][j].cap_name)                                       
                            n_w_top=[]
                            n_w_top.append(wire_2_2)
                            n_w_top.append(new_assign_top)
                            n_w_top.append(index)
                            cap.wire_length_top.append(n_w_top)
                            wire_length_top.append(n_w_top)                                        

#print('cap.wire_length_top', cap.wire_length_top)
Only_per_cap_ratio=[]

for i in range (len(obj)):
    flag=0
    for j in range (len(obj[i])):
        ind=obj[i][j].cap_name
        color_r= my_color[ind-1]
        if len(obj[i][j].inter_connected)!=0 and obj[i][j].detailed_route_mark==0 and obj[i][j].cap_name not in All_conn :
            condition_check=0
            #print('coming here', obj[i][j].inter_connect)
            if len(obj[i][j].inter_connected)==1 and obj[i][j].x_coordinate_new<0:
                
                condition_check=obj[i][j].x_coordinate_new
                
            elif len(obj[i][j].inter_connected)>1 and obj[i][j].top_sign>0:
                condition_check=obj[i][j].top_sign

                                     

            track_number=cap.num                                                        
            if obj[i][j].top_sign>=0:
                print('r u coming for me', detailed_tr)
                if space_requirement=='Unequal':
                    track_number=obj[i][obj[i][j].lowest_y_j].channel_width_r
                (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][obj[i][j].lowest_y_j].track_right_detailed, detailed_tr)
                track_top=obj[i][obj[i][j].lowest_y_j].track_right_detailed_top[index]
                print('tracks values and direction',obj[i][obj[i][j].lowest_y_j].inter_connect, track_one, track_top, obj[i][obj[i][j].lowest_y_j].track_right_detailed, obj[i][obj[i][j].lowest_y_j].track_right_detailed[index])
            else:
                if space_requirement=='Unequal':
                    track_number=obj[i][obj[i][j].lowest_y_j].channel_width_l                
                (track_one, detailed_tr, index)=Global_detailed_routing_main.track_selection(obj[i][obj[i][j].lowest_y_j].track_left_detailed, detailed_tr)
                track_top=obj[i][obj[i][j].lowest_y_j].track_left_detailed_top[index]            
        
            tracks.append(track_one) 
            #(x_value_j, y_min_cal_j_r)=Global_detailed_routing_main.xy_value(track_one, obj[i][j].inter_connected, width)
            x_value_j=obj[i][obj[i][j].lowest_y_j].x_coordinate_new
            y_min_cal_j_r=obj[i][obj[i][j].lowest_y_j].y_coordinate_new

            new_assign=[]
            new_assign.append(round(track_one,5))
            htrack=y_min_cal_j_r-((cap.h)/2)+cap.pin_y+Layers_dict['M2']['Width']/2 
            
            Via_Num=Via_Num+1
            obj[i][j].via_number=1                         

            wire_2=abs(x_value_j-track_one)-(cap.w/2)+obj[i][j].inter_connect_length
            
            sx_channel=(track_number+1)*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
            
            fl=horizontal(i, track_one, y_min_cal_j_r, x_value_j, horizontal_track_new, sx_channel, htrack)                    
            new_f=fl.horizontal_routing()

            if new_f==1:
                htrack=fl.horizontal_track_assign()
                cap.a_t_h_ratio.append(round(htrack,5))
            new_assign.append(round(htrack,5))
            h_t=fl.insert(round(htrack,5))
            horizontal_track_new.append(h_t)   
            new_assign.append(obj[i][j].cap_name)

                
            #htrack_l=(minimum_y-((cap.h)/2)-(cap.sy/(cap.num_h)))                    
                                      
            n_w=[]
            n_w.append(wire_2)
            n_w.append(new_assign)
            n_w.append(index)
            cap.wire_length.append(n_w)
            wire_length_bottom.append(n_w)  
            #htrack_l=minimum_y-cap.w/2-cap.sy
            
            htrack_l=(minimum_y-((cap.h)/2)-Layers_dict['M2']['Width']/2-Layers_dict['M2']['Space']) 
            Global_detailed_routing_main.Detailed_route_performed(obj, i, j)  

            if circuit_type=='General':
                y_value_max=y_min_cal_j_r
                
                x_top=x_value_j
                new_assign_top=[]
                new_assign_top.append(round(track_top,5))
                htrack_top=y_value_max+((cap.h)/2) -cap.pin_y-Layers_dict['M2']['Width']/2
                
                sx_channel_top=(track_number+1)*(Layers_dict['M3']['Space']+Layers_dict['M3']['Width'])
                
                fl_b_top=horizontal(i, track_top, y_value_max, x_top, horizontal_track_new_top, sx_channel_top, htrack_top)                                            
                new_f_top=fl_b_top.horizontal_routing_top()
                
                if new_f_top==1: 
                                   
                    htrack_top=fl_b_top.horizontal_track_assign_top()
                    cap.a_t_h_ratio.append(round(htrack_top,5))
                new_assign_top.append(round(htrack_top,5))
    
                h_t_top=fl_b_top.insert(round(htrack_top,5))
                horizontal_track_new_top.append(h_t_top)
                                            
                wire_2_2=abs(x_top-track_top)+obj[i][j].inter_connect_length     -(cap.w/2)                                                                            
    
                Layout_top_bottom_one_side_1.Horizontal_track_plot_top(track_top, htrack_top, cap.w, cap.h, x_top, y_value_max, cap.line_w, color_r, new_f_top, Layers_dict, Terminal_list, cap)
                
                new_assign_top.append(obj[i][j].cap_name)     
                n_w_top=[]
                n_w_top.append(wire_2)
                n_w_top.append(new_assign_top)
                n_w_top.append(index)
                cap.wire_length_top.append(n_w_top)
                wire_length_top.append(n_w_top)  
                
            Layout_top_bottom_one_side_1.Horizontal_track_plot(track_one, htrack, cap.w, cap.h, x_value_j, y_min_cal_j_r, cap.line_w, color_r, new_f, Layers_dict, Terminal_list, cap)            
            #plt.plot([track_one, track_one],[htrack, htrack_l], color=color_r, linewidth=cap.line_w)  
            
if space_requirement=="Equal":
    x_coor=[]
    for i in range (len(obj)):
        for j in range (len(obj[i])):
            x_coor.append(obj[i][j].x_coordinate_new)
    
    x_uni=set(x_coor)
    x_uni_1=list(x_uni)
    x_uni_1.sort()
    
    last_track=[]
    first_track=[]
    
    parallel_count=0
    
    counter_for_side=0
    #via_num_MSB=[]
    for i in range (len(obj)):
        flag=0
        via_n=0
        parallel_count_1=0
        for j in range (len(obj[i])):
            ind=obj[i][j].cap_name
            color_r= my_color[ind-1]
            if len(obj[i][j].inter_connected)==new_list[i]  and obj[i][j].detailed_route_mark==0 :        
                #print('obj[i][j].inter_connected',i+1)
                track_uniq=set(detailed_tr)
                track_uniq_1=list(track_uniq)
                track_uniq_1.sort()      
                t_h=[]
                chnl_t=[]
                min_x=0
                v_t_right=0
                last_cnt=0
                x_val=0
                flag=0  
                index=0
                for kk in range (len(x_uni_1)//2,len(x_uni_1)-1):   
                    same_channel=[]
                    for jj in range (len(track_uniq_1)):        
                        if x_uni_1[kk] < track_uniq_1[jj] and x_uni_1[kk+1] > track_uniq_1[jj]:                        
                            if track_uniq_1[jj] not in t_h:
                                same_channel.append(track_uniq_1[jj])
                                t_h.append(track_uniq_1[jj])  
                
                    if len(same_channel)<=2:     
                        min_x=x_uni_1[kk]                    
                        for cnt in range (2, cap.num+1): 
                            if counter_for_side%2==0:                                 
                                v_t_right=min_x+cap.w/2+(cnt*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']))
                                x_val=min_x
                                index=cnt
                            else:
                                v_t_right=-min_x-cap.w/2-(cnt*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width']))
                                x_val=-min_x
                                index=cnt
                            last_cnt=cnt
                            if round(v_t_right,5) not in detailed_tr and round(-v_t_right,5) not in detailed_tr :
                                flag=1
                                break
                        if flag==1:
                            break
                        #break
                
                tracks.append(v_t_right)
    
                v_next=v_t_right
    
                counter_for_side=counter_for_side+1
    
                detailed_tr.append(round(v_t_right,5))
                detailed_tr.append(round(v_next,5))
                #detailed_tr.append(round(min_x+cap.w/2+((last_cnt+1)*cap.sx)/(cap.num),5))
                 
                Via_Num=Via_Num+1
                obj[i][j].via_number=1                         
         
                (x_value_j_min, y_min_cal_j_r)=Global_detailed_routing_main.xy_value(v_next, obj[i][j].inter_connected, width)
    
                
                            
                x_value_j_min=x_val
                
    
                
                h_t=y_min_cal_j_r-cap.h/2+cap.pin_y+Layers_dict['M2']['Width']/2
                #htrack_l=minimum_y-cap.h/2-cap.sy
    
                if len(obj[len(new_list)-1][j].inter_connected)==new_list[len(new_list)-1]:
                    last_track.append(v_next)
                    last_track.append(h_t)
    
                new_w_b=[]
                new_w_b.append(round(v_next,5))
                new_w_b.append(round(h_t,5))
                new_w_b.append(obj[i][j].cap_name)
    
                wire_b = obj[i][j].inter_connect_length + abs(x_value_j_min-v_next)-cap.w/2 
                
                wire_a=[]
                wire_a.append(wire_b)
                wire_a.append(new_w_b)
                wire_a.append(index)
                wire_length_bottom.append(wire_a)
                cap.wire_length.append(wire_a)                            
    
                Global_detailed_routing_main.Detailed_route_performed(obj, i, j)                      
                cap_count=[]
                for j_1 in range (len(obj[i])):
                    cap_c=0               
                    if round(obj[i][j_1].y_coordinate_new, 3)==round(y_min_cal_j_r,3): 
    
                        for j_2 in range (len(obj[i])):
                            if round(obj[i][j_1].x_coordinate_new,3)==round(obj[i][j_2].x_coordinate_new,3):
                                cap_c=cap_c+1
                                
                    cap_count.append(cap_c)
                
                for j_1 in range (len(obj[i])):
                    cap_c=0               
                    if round(obj[i][j_1].y_coordinate_new, 3)==round(y_min_cal_j_r,3): 
                        for j_2 in range (len(obj[i])):
                            if round(obj[i][j_1].x_coordinate_new,3)==round(obj[i][j_2].x_coordinate_new,3):
                                cap_c=cap_c+1
                    
                    if cap_c==max(cap_count) and i+1==Device_Name[len(Device_Name)-1]:
                        parallel_count=parallel_count+1
                        parallel_count_1=parallel_count_1+1
    
                # htrack_l=(minimum_y-((cap.h)/2)-(cap.sy/(cap.num_h)))  
                htrack_l=(minimum_y-((cap.h)/2)-Layers_dict['M2']['Width']/2-Layers_dict['M2']['Space'])                   
    
                
                    
                flag=0
                
                var='D'+str(int(obj[i][j].cap_name))
                #Layout_top_bottom_one_side_1.Horizontal_track_plot(v_next, h_t, cap.w, cap.h, x_value_j_min, y_min_cal_j_r, cap.line_w, color_r, flag,  Layers_dict, Terminal_list, cap)
                Layout_top_bottom_one_side_1.trunk_routing(v_next, htrack_l, h_t, Layers_dict, Terminal_list, cap, color_r, index, var) 
                Layout_top_bottom_one_side_1.trunk_routing_via(v_next, h_t, Layers_dict, Terminal_list, cap)
    
                (x_value_j_max, y_max_cal_j_r)=Global_detailed_routing_main.xy_value_top(-v_next, obj[i][j].inter_connected, width) 
    
                (i_idx, j_idx)=Global_detailed_routing_main.capacitor_index(obj, -x_value_j_min, y_max_cal_j_r)
                
                wire_b = obj[i][j].inter_connect_length + abs(x_value_j_min-v_next)-cap.w/2 
 
                if circuit_type=='General':
                    tr_idx=0
                    flag_tr=0
                    if -x_value_j_min>-v_next:
                        for tr in range (len(obj[i][j_idx].track_left_detailed)):
                            if obj[i][j_idx].track_left_detailed[tr]==-v_next:
                                tr_idx=tr
                                flag_tr=1
                                break
                                
                    if -x_value_j_min<-v_next:
                        for tr in range (len(obj[i][j_idx].track_right_detailed)):
                            if obj[i][j_idx].track_right_detailed[tr]==-v_next:
                                tr_idx=tr
                                break                
        
                    h_t_u=y_max_cal_j_r+cap.h/2-cap.pin_y-Layers_dict['M2']['Width']/2
                    htrack_u=maximum_y+((cap.h)/2) 
        
                    if len(obj[len(new_list)-1][j].inter_connected)==new_list[len(new_list)-1]:
                        first_track.append(v_next)
                        first_track.append(h_t_u)
        
                    new_w_u=[]
                    new_w_u.append(round(-v_next,5))
                    new_w_u.append(round(h_t_u,5))
                    new_w_u.append(obj[i][j].cap_name)
        
                    
                    
                    wire_u=[]
                    wire_u.append(wire_b)
                    wire_u.append(new_w_u)
                    wire_u.append(index)
                    wire_length_top.append(wire_u)
                    cap.wire_length_top.append(wire_u) 
        
                    Layout_top_bottom_one_side_1.Horizontal_track_plot_top(-v_next, h_t_u, cap.w, cap.h, -x_value_j_min, y_max_cal_j_r, cap.line_w, color_r, flag,  Layers_dict, Terminal_list, cap)
            
            
all_delays=[]
for i in range (len(new_list)):
    dela=[]
    for j in range (len(delay_list)):
        if delay_list[j][1]==i+1:
            dela.append(delay_list[j][0])
    all_delays.append(dela)

if circuit_type=='Split':
    w_per_cap=[]
    wr=obj[cap.bridge][0].inter_connect_length+bridge_cap_bottom
    w_per_cap.append(wr)
    w_per_cap.append(cap.bridge+1)
    Only_per_cap_ratio.append(w_per_cap)
      
Bridge_wires_1_new=[] 

total_bottom_length=0    
(bridge_first_last, Only_per_cap_ratio, last_h, Bridge_wires_1_new, Via_Num, total_bottom_length, new_connecting_wire)=Layout_top_bottom_one_side_1.Bridge_connection(cap.wire_length, minimum_y, cap.h, cap.sy, cap.num_h, my_color, cap.a_t_h_ratio, Via_Num, Device_Name, cap.line_w, total_bottom_length, All_conn, Only_per_cap_ratio, Layers_dict, Terminal_list, cap, obj)
if circuit_type=='General':
    (bridge_first_last_top, Only_per_cap_ratio_top, first_h, Bridge_wires_1_new_top, Via_Num, total_top_length, new_connecting_wire_top)=Layout_top_bottom_one_side_1.Bridge_connection_top(cap.wire_length_top, maximum_y, cap.h, cap.sy, cap.num_h, my_color, cap.a_t_h_ratio, Via_Num, Device_Name, cap.line_w, total_bottom_length, All_conn, Only_per_cap_ratio, Layers_dict, Terminal_list, cap, obj)

new_length_BS=[]
Inter_con=[]
Via_per_cap=[]
Res_only_via=[]
Via_per_cap_top=[]
for i in range (len(obj)):
    via_n=0
    via_t=0
    for j in range (len(obj[i])):
        via_n=via_n+obj[i][j].via_number
        via_t=via_t+obj[i][j].via_number_top
    #if obj[i][j].via_number!=0:
    #print('what is your via', i, via_n) 
    count_n=0                    
    for j in range(len(wire_length_bottom)):
        len_1=len(wire_length_bottom[j][1]) 
          
        if wire_length_bottom[j][1][len_1-1]==i+1:
            count_n=count_n+1
            #print('what is your via', i, count_n, obj[wire_length_bottom[j][1][len_1-1]-1][0].inter_connect, obj[wire_length_bottom[j][1][len_1-1]-1][0].via_number) 
            
    if count_n>1:
        via_n=via_n+count_n
        
    v_n=[]
    v_n.append(via_n)
    v_n.append(i+1)
    v_t=[]
    v_t.append(via_t)
    v_t.append(i+1)
    #print('what is your via after count', i, via_n, count_n) 
    Via_per_cap.append(v_n)  
    Via_per_cap_top.append(v_t)

Actual_via_num_bottom=0
for i in range (len(Via_per_cap)):
    Actual_via_num_bottom=Actual_via_num_bottom+Via_per_cap[i][0]

Actual_via_num_top=0
for i in range (len(Via_per_cap_top)):
    Actual_via_num_top=Actual_via_num_top+Via_per_cap_top[i][0]
      
lengt_list=[]
for i in range (len(obj)):
    lengt=Only_per_cap_ratio[i][0]
    inter_len=0
    for j in range (len(obj[i])):
        if len(obj[i][j].inter_connected)!=0  : 
            inter_len=inter_len+obj[i][j].inter_connect_length
    
    Inter_con.append(inter_len)
    res=lengt*cap.res_per_length+Via_per_cap[i][0]*cap.res_per_via
    lengt_list.append(lengt)

    capacitance_after.append(lengt*cap.cap_per_length_bottom)
    Resistance_after.append(res)
    Res_only_via.append(Via_per_cap[i][0]*cap.res_per_via)
    new_length_BS.append(lengt)
Frequency_list=[]
if circuit_type=="Binary" or circuit_type=='Split':
    lengt_list=[]
    extra_cap=0
    for i in range (len(obj)):
        lengt=Only_per_cap_ratio[i][0]
        inter_len=0
        for j in range (len(obj[i])):
            if len(obj[i][j].inter_connected)!=0  : 
                inter_len=inter_len+obj[i][j].inter_connect_length
        
        Inter_con.append(inter_len)
        lengt_cap=lengt
        if i ==len(new_list)-1 or i ==len(new_list)-2 :        
            lengt=lengt/cap.Parallel_wire_number
            lengt_cap=lengt_cap*cap.Parallel_wire_number
            Via_per_cap[i][0]=Via_per_cap[i][0]/(cap.Parallel_wire_number*cap.Parallel_wire_number)
    
        res=lengt*cap.res_per_length+Via_per_cap[i][0]*cap.res_per_via
        lengt_list.append(lengt)    
    
        capacitance_after.append(lengt_cap*cap.cap_per_length_bottom)
        extra_cap=extra_cap+inter_len*cap.cap_per_length_bottom
        Resistance_after.append(res)
        Res_only_via.append(Via_per_cap[i][0]*cap.res_per_via)
        new_length_BS.append(lengt)
    
    
    for i in range (len(new_list)):
        Frequency_list.append(10**(-6)/(cap.time_constant*((capacitance_after[i])+new_list[i]*cap.unit_cap)*Resistance_after[i]*10**(-15)))
    
    


min_track=min(tracks)
Area_1=Evaluation_Unequal_Channel.Area(row, colomn, cap.w, cap.h, cap.sx, cap.sy, last_h, minimum_y)

v_num=0
for i in range (len(Via_per_cap)):
    v_num=v_num+Via_per_cap[i][0]
   

Resistance_large_cap=Only_per_cap_ratio[len(Only_per_cap_ratio)-1][0]*cap.res_per_length
for i in range (len(Only_per_cap_ratio)):
    total_bottom_length=total_bottom_length+Only_per_cap_ratio[i][0]


for i in range (len(Only_per_cap_ratio)):
    total_bottom_length=total_bottom_length+Only_per_cap_ratio[i][0]
Cap_bs_1= cap.cap_per_length_bottom*total_bottom_length

C_bb=Evaluation_Unequal_Channel.Bottom_bottom_parasitic(cap.wire_length, Bridge_wires_1_new, colomn, cap.sx, cap.w, minimum_y, cap.num_h, bridge_first_last, cap.sy, cap.spacing, cap.cap_per_length_coupling_32, cap.cap_per_length_coupling_64, cap.cap_per_length_coupling_96, cap.cap_per_length_coupling_128, cap.cap_per_length_coupling_160, cap.cap_per_length_coupling_192)
C_tb_f=Evaluation_Unequal_Channel.Top_bottom_parasitic(cap.wire_length, colomn, cap.sx, cap.w, cap.h, minimum_y, cap.num_h, bridge_first_last, cap.sy, cap.spacing, cap.cap_per_length_coupling_32, cap.cap_per_length_coupling_64, cap.cap_per_length_coupling_96, cap.cap_per_length_coupling_128, cap.cap_per_length_coupling_160, cap.cap_per_length_coupling_192)


Bridge_wires_1_new.append(minimum_y-cap.h)
     
x_terminal=[]
y_terminal=[]
for i in range (len(Terminal_list)):
    x_terminal.append(Terminal_list[i]['rect'][0])
    x_terminal.append(Terminal_list[i]['rect'][2])
    y_terminal.append(Terminal_list[i]['rect'][1])
    y_terminal.append(Terminal_list[i]['rect'][3])    

# max_x_terminal=max(x_terminal)
# max_y_terminal=abs(min(y_terminal))

max_x_terminal=max_x_coor+cap.w+4*(Layers_dict['M1']['Space']+Layers_dict['M1']['Width'])
max_y_terminal=max_y_coor+cap.h+4*(Layers_dict['M2']['Space']+Layers_dict['M2']['Width'])

cap_layer_dict={}

bbox_r=[]

bounding_box_x=0
bounding_box_y=0
bounding_box_x_max=2*max_x_terminal
bounding_box_y_max=2*max_y_terminal
#bounding_box_y_max=2*(max_y_coor+cap.h/2+2*(Layers_dict['M2']['Space']+Layers_dict['M2']['Width']))*cap.scale_factor


Layout_top_bottom_one_side_1.CC_plot(obj, Device_Name, mat, row, colomn, cap.w, cap.sx, cap.h, cap.sy, my_color, cap.line_w, cap, Terminal_list)


bbox_r.append(int(round(bounding_box_x,1)))
bbox_r.append(int(round(bounding_box_y,1)))
bbox_r.append(int(round(bounding_box_x_max,1)))
bbox_r.append(int(round(bounding_box_y_max,1)))
cap_layer_dict['bbox']=bbox_r   

for i in range (len(Terminal_list)):
    Terminal_list[i]['rect'][0]=int(round(Terminal_list[i]['rect'][0]+max_x_terminal, 1)) 
    Terminal_list[i]['rect'][1]=int(round(Terminal_list[i]['rect'][1]+max_y_terminal, 1)) 
    Terminal_list[i]['rect'][2]=int(round(Terminal_list[i]['rect'][2]+max_x_terminal, 1))  
    Terminal_list[i]['rect'][3]=int(round(Terminal_list[i]['rect'][3]+max_y_terminal, 1))     

with open('CAP_12F.json', "rt") as fp:
    l = json.load(fp)
                            
for i in range (len(obj)):
    for j in range (len(obj[i])):
        new_x, new_y = obj[i][j].x_coordinate_new, obj[i][j].y_coordinate_new
        for term in l['terminals']: 
            unit_capacitor=Layout_top_bottom_one_side_1.unit_cap(term['layer'], term['netName'])
            llx, lly, urx, ury = term['rect']
            Terminal_list.append(unit_capacitor.segment(llx+new_x-cap.w/2+max_x_terminal, lly+new_y-cap.h/2+max_y_terminal , urx+new_x-cap.w/2+max_x_terminal, ury+new_y-cap.h/2+max_y_terminal , term['netType'])) 


cap_layer_dict['terminals']=Terminal_list
#cap_layer_dict['terminals']=Terminal_list
    
with open('Cap_layers_DAC_6_bit.json', "w") as fp:
    fp.write(json.dumps(cap_layer_dict, indent=2)+'\n') 

Area_1=Evaluation_Unequal_Channel.Area(row, colomn, cap.w, cap.h, cap.sx, cap.sy, last_h, minimum_y)    
#plt.axis('off')
           
plt.savefig('DAC_general.png', dpi=300)        
plt.show()
# # #sigma_del_C_ON,  D_k, sigma_c_t, C_ON_2, Del_sys, C_del_t, Del_sys_p, C_del_t_p
Parasitic_top=(row-1)*colomn*cap.sy+(colomn-1)*cap.sx
(M_sys, C_star)=Evaluation_Unequal_Channel.Mismatch(Device_Name, mat, row, colomn, cap.w, cap.h, cap.sx, cap.sy, cap.t0, cap.y_ppm, new_list, obj)
if circuit_type=="Binary":
    (sigma_del_C_ON, D_k, sigma_c_t_list, C_on, Del_C_ON, C_del_t,  Del_C_new_ON, C_del_t_p, cov_v_list, only_del_sys, dNL, iNL, max_dn, max_in)=Evaluation_Unequal_Channel.INL_DNL(Device_Name, cap.unit_cap, new_list, mat, row, colomn, cap.w, cap.h, cap.sx, cap.sy, cap.t0, cap.y_ppm, Parasitic_top, Sigma, eq_1, cap.rho_u, cap.Af_1, cap.d0, obj)


