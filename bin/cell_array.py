#!/usr/bin/env python

import numpy
import gdspy
import json
import os
from align.gdsconv.gds2json import convert_GDS_GDSjson
from align.gdsconv.gds2lefjson import GDS2_LEF_JSON
import random
import sys
# Read configuration from the JSON file
with open('config.json', 'r') as json_file:
    config = json.load(json_file)

layers = config["layers_file"]
gds_dir = config["gds_dir"]
scale = 1e6
units = 1e-6
rows = config["rows"]
columns = config["columns"]
placement_pat = config["placement"]
m2_width = config["m2_width"]
m3_width = config["m3_width"]
m4_width = config["m4_width"]
mos_type = config["mos_type"]
mid_rout = config["mid_rout"]
high_rout = config["high_rout"]
source_body = config["source_body"]
print("\n\nGenerating constrained layout with following specifications.\n ")
print(f"Layers      :   {layers}")
print(f"Gds_dir     :   {gds_dir}")
print(f"Scale       :   {scale}")
print(f"Units       :   {units}")
print(f"Rows        :   {rows}")
print(f"Columns     :   {columns}")
print(f"MOS Type    :   {mos_type}")
print(f"Placement   :   {placement_pat}")
print(f"M2_Width    :   {m2_width}")
print(f"M3_Width    :   {m3_width}")
print(f"M4_Width    :   {m4_width}")


assert len(placement_pat) == columns, "No. of coumns should match placement pattern. Please try again !!!"
#assert any(elem in ["N", "P"] for elem in your_variable), "The variable should contain characters 'N' or 'P'. Please try again !!!"

placement = []
i = 'A'
for p in placement_pat:
	if p == i:
		placement.append(1)
	else:
		placement.append(0)

print(placement)

def print_error():
    print("All necessary configurations not provided. Please check config.json")

if  gds_dir == "" or layers == "" or scale is None or units is None or rows is None or columns is None:
    print_error()
    exit()

class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._oX = oX 
        self._oY = oY
        self._sX = sX
        self._sY = sY
    def __str__(self):
        return f'({str(self._oX)} {str(self._oY)} {str(self._sX)} {str(self._sY)})'

class Instance:
    def __init__(self, name = "", tr = Transform()):
        self._name = name
        self._tr   = tr
        self._modu = None
    def __str__(self):
        return f'{self._name} {str(self._tr)}'

class Module:
    def __init__(self, name = "", leaf = False):
        self._name      = name
        self._instances = list()
        self._added     = False
        self._leaf      = leaf
        self._fname     = ""
        self._cell      = None
    def __str__(self):
        s = f"{self._name} '{self._fname}' {self._cell}"
        for i in self._instances:
            s += f' [{str(i)} {i._modu._name}]'
        return s
    def add(self):
        print(f'working on cell {self._name}')
        for i in self._instances:
            if i._modu:
                if not i._modu._added:
                    i._modu.add()
                bbox = i._modu._cell.get_bounding_box()
                angle, refl = 0, False
                oX, oY = i._tr._oX/scale, i._tr._oY/scale
                if i._tr._sX < 0:
                    angle = 180
                    refl = (i._tr._sY > 0)
                else:
                    refl = (i._tr._sY < 0)
                print(f'{self._name} creating reference of {i._name} at {(oX,oY)} {refl} {angle})')
                ref = gdspy.CellReference(i._modu._cell, (oX, oY), x_reflection = refl, rotation = angle)
                if not self._cell:
                    self._cell = gdspy.Cell(self._name)
                self._cell.add(ref)
        self._added = True


#################################################################################################################################################################################################################
#################################################################################################################################################################################################################
#####################################################################################STARTER: NOTHING SPECIFIC TO CIRCUIT########################################################################################
#################################################################################################################################################################################################################
#################################################################################################################################################################################################################

gdscell = dict()
#Reading all the gds files of black boxes
if (gds_dir):
    if not os.path.isdir(gds_dir):
        print(f'{gds_dir} not found')
        exit()
 
    all_files = os.listdir(gds_dir)
    gds_files = [file for file in all_files if file.lower().endswith('.gds')]

layers_specs_sacle = 1e3
#Reading layers.json file
def readLayerInfo(layerfile): 
    layers = dict()
    layerSpecs = dict()
    layernames = dict()
    labellayers = dict()
    with open(layerfile) as fp:
        layerdata = json.load(fp)
        if "Abstraction" in layerdata:
            for l in layerdata["Abstraction"]:
                if "Layer" in l and "GdsLayerNo" in l:# and "Direction" in l:
                    layer = l["Layer"]      #Layer Name (M1)
                    glno1 = l["GdsLayerNo"]    #Layer no. (15)
                    glno2 = dict()  #Dict for storing different datatypes of layer
                    specs = dict()
                    layernames[glno1] = layer   #Dict of layernames where key is layer number and value is layer name
                    if "GdsDatatype" in l:
                        for key, idx in l["GdsDatatype"].items():
                            glno2[idx] = key    #Storing values of gds data types where key is the Data type No (32) (idx) and  value is the data type name (Pin) (key)
                            if "Label"== key:   #If its data type of "Label"
                                labellayers[(glno1, idx)] = glno1 #e.g. labelayers[(17,20)] = 17 WHICH IS FOR M2 Label
                            elif "Pin"== key:
                                labellayers[(glno1, idx)] = glno1 #e.g. labellayers[(17,32)] = 17 WHICH IS FOR M2 Pin
                    if "LabelLayerNo" in l:
                        for ll in l["LabelLayerNo"]:
                            if len(ll) == 2:
                                labellayers[(ll[0], ll[1])] = glno1
                            elif len(ll) == 1:
                                labellayers[(ll[0], 0)] = glno1
                    layers[layer] = glno2
                    if "Width" in l:
                        specs["Width"] = l["Width"]/layers_specs_sacle
                    if "WidthX" in l:
                        specs["WidthX"] = l["WidthX"]/layers_specs_sacle
                    if "WidthY" in l:
                        specs["WidthY"] = l["WidthY"]/layers_specs_sacle
                    if "SpaceX" in l:
                        specs["SpaceX"] = l["SpaceX"]/layers_specs_sacle
                    if "SpaceY" in l:
                        specs["SpaceY"] = l["SpaceY"]/layers_specs_sacle
                    if "Pitch" in l:
                        specs["Pitch"] = l["Pitch"]/layers_specs_sacle
                    if "VencA_L" in l:
                        specs["VencA_L"] = l["VencA_L"]/layers_specs_sacle
                    if "VencA_L" in l:
                        specs["VencA_H"] = l["VencA_H"]/layers_specs_sacle
                    if "VencA_L" in l:
                        specs["VencP_L"] = l["VencP_L"]/layers_specs_sacle
                    if "VencA_L" in l:
                        specs["VencP_H"] = l["VencP_H"]/layers_specs_sacle
                    if "Direction" in l:
                        specs["Direction"] = l["Direction"]
                    layerSpecs[layer] = specs
    return (layers, layernames, labellayers, layerSpecs)

layers, layernames, labellayers, layerSpecs = readLayerInfo(layers)

#################################################################################################################################################################################################################
#################################################################################################################################################################################################################
#####################################################################################STARTING LAYOUT BUILDING####################################################################################################
#################################################################################################################################################################################################################
#################################################################################################################################################################################################################

#Returns the coordinates of all the polygons in a gds file in an organized dict for different layers 
def get_polygon_coordinates(cell):
    polygon_coordinates = {}
    for polygon_set in cell.polygons:
        layer_number = polygon_set.layers[0]
        datatype = polygon_set.datatypes[0]
        key = (layer_number, datatype)
        for polygon in polygon_set.polygons:
            coordinates = polygon.flatten()
            if key in polygon_coordinates:
                polygon_coordinates[key].append(coordinates)
            else:
                polygon_coordinates[key] = [coordinates]
    return polygon_coordinates

def find_extreme_coordinate(arrays, extreme='max', axis='x'):
    index = 0 if axis == 'x' else 1
    extreme_coordinate = arrays[0][index]
    for array in arrays:
        for i in range(index,len(array),2):
          coordinate = array[i]
          if extreme == 'max':
              extreme_coordinate = max(extreme_coordinate, coordinate)
          elif extreme == 'min':
              extreme_coordinate = min(extreme_coordinate, coordinate)
          else:
              raise ValueError("Invalid value for 'extreme'. Use 'max' or 'min'.")
    return round(extreme_coordinate, 3)


all_polygon_coordinates = {}
processed_cells = set() #Stores information of the PCELLs Polygons
new_cells = list()
new_cell = gdspy.Cell("Combined")
new_cells.append(new_cell)
wl,hl,wr,hr,wm,hm,wb,hb,wp,hp = 0,0,0,0,0,0,0,0,0,0 #Widths of individual PCELLs
for gds in gds_files: 
    lib = gdspy.GdsLibrary(infile=gds_dir+'/'+gds)
    cell = lib.top_level()[0]
    gds_polygon_coordinates = {}
    cell.flatten()
    cell_polygon_coordinates = get_polygon_coordinates(cell)
    gds_polygon_coordinates[cell.name] = cell_polygon_coordinates
    #print("CHECK HERE ********", gds)
    all_polygon_coordinates[gds] = gds_polygon_coordinates
    bounding_box = cell.get_bounding_box()
    ll, ur = bounding_box
    width = ur[0]- ll[0]  
    height = ur[1] - ll[1]
    gap_offset = config["eg_gap"] #For EG horizontal spacing >= 0.4
    if mos_type == "N":
        if "MID" in cell.name:      #NOTE: Additive terms are for satisfying DRCs
            wm = width + gap_offset
            hm = height - 0.308
        elif "LEFT" in cell.name:
            wl = width + gap_offset
            hl = height - 0.308
        elif "RIGHT" in cell.name:
            wr = width 
            hr = height - 0.308
        elif "BC" in cell.name:
            wb = width        
            hb = height - 0.308
    else:
        if "PMOS" in cell.name:
            wp = width + gap_offset
            hp = height + 0.034 
           
        elif "BC" in cell.name:
            wb = width + gap_offset
            hb = height + 0.034

    new_cells.append(cell)

#Finding effective width of each black boxes
#This block can differentiate N and P layouts
for cell in new_cells:
    if "LEFT" in cell.name:

        wl_eff = round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2] - all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][0],3)+gap_offset/2

    elif "RIGHT" in cell.name:

        wr_eff = round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2] - all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][0] ,3)+gap_offset/2

    elif "MID" in cell.name:

        wm_eff = round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2] - all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][0] ,3)+gap_offset

    elif "PMOS" in cell.name:

        wp_eff = round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2] - all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][0] ,3)+gap_offset
    
rectangles = list()


#print("PLACING CELLS IN THIS BLOCK \n\n\n\n")
for cell in new_cells:
    if "LEFT" in cell.name: 

        #print("Instantiating the PCELLS of MOS")  
        offset = 2*round((all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][2]-all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2]),3) #Width of the triple n_well 
        bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][1],3))
        topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][5],3))
        for count2 in range(0,int(rows)): 
            #print("\tInstantiating PCELLS for left column")
            #if "MID" in gds:
            oX, oY = 0 , 0 + count2*hl
            #print("Instantiating",cell.name," at ",oX,",",oY)              
            ref = gdspy.CellReference(cell, (oX, oY))
            finY = oY
            for count3 in range (1,4):   
                rectangles.append(gdspy.Rectangle((oX+(offset/2), finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]), (oX+wl - (offset/2)-gap_offset/2 , finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the LEFT PCELLs   (Vertical Space)
            for count3 in range ( 4,8):   
                rectangles.append(gdspy.Rectangle((oX+(offset/2), finY+hl+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wl - (offset/2)-gap_offset/2 , finY+hl+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the LEFT PCELLs   (Vertical Space)
            if gap_offset !=0:  #Only if the EG gap is not 0              
                for count3 in range ( 0,22): 
                    rectangles.append(gdspy.Rectangle((oX+wl-(offset/2)- gap_offset, finY+bottomFin2bottomBB+(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wl-(offset/2)-gap_offset/2 , oY+bottomFin2bottomBB+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the LEFT PCELLs   (Horizontal space)(right side)
            new_cell.add(ref)
            
    if "MID" in cell.name:

        offset = 2*round((all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][2]-all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2]),3) #Width of the triple n_well
        bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][1],3))
        topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][5],3))
        #print("Instantiating the PCELLS of MOS")
        for count in range(0,int(columns)-2): 
            for count2 in range(0,int(rows)):
                oX, oY = wl + count*(wm -offset) -offset , 0 + count2*hm
                ref = gdspy.CellReference(cell, (oX, oY))          
                finY = oY
                for count3 in range (1,4):   
                    rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]), (oX+wm - (offset/2)-gap_offset/2 , finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the MID PCELLs   (Vertical Space)
                for count3 in range ( 4,8):   
                    rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+hm+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wm - (offset/2)-gap_offset/2 , finY+hl+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the MID PCELLs   (Vertical Space)
                if gap_offset !=0:  #Only if the EG gap is not 0  
                    for count3 in range ( 0,22):   
                        rectangles.append(gdspy.Rectangle((oX+wm-(offset/2)- gap_offset, finY+bottomFin2bottomBB+(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wm-(offset/2)-gap_offset/2 , oY+bottomFin2bottomBB+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the MID PCELLs   (Horizontal space)(right side)
                        rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+bottomFin2bottomBB+(count3)*(layerSpecs['Fin']['Pitch'])), (oX + (offset/2) , finY+bottomFin2bottomBB+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the MID PCELLs   (Horizontal space)(left side)
                new_cell.add(ref)
                
    if "RIGHT" in cell.name:
        offset = 2*round((all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][2]-all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2]),3) #Width of the triple n_well
        wr_eff = all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2]
        bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][1],3))
        topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][5],3))
        #print("Instantiating the PCELLS of MOS")    
        for count2 in range(0,int(rows)): 
            oX, oY = wl-offset+(wm-offset)*(int(columns)-2) , 0 + count2*hr
            #print("Instantiating",cell.name," at ",oX,",",oY)             
            #print(width, height)
            ref = gdspy.CellReference(cell, (oX, oY))     
            finY = oY
            for count3 in range (1,4):   
                rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]), (oX+wr - (offset/2) , finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the RIGHT PCELLs   (Vertical Space)
            for count3 in range ( 4,8):   
                rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+hr+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wr - (offset/2), finY+hl+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the RIGHT PCELLs   (Vertical Space)
            
            if gap_offset !=0:  #Only if the EG gap is not 0  
                for count3 in range ( 0,22):   
                        rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+bottomFin2bottomBB+(count3)*(layerSpecs['Fin']['Pitch'])), (oX + (offset/2) , finY+bottomFin2bottomBB+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the RIGHT PCELLs   (Horizontal space)(left side)
            new_cell.add(ref)

    if "PMOS" in cell.name:
        offset = round((all_polygon_coordinates[cell.name+".gds"][cell.name][4,0][0][2]-all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2]),3) #Width of the triple n_well
        bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][4,0][0][1],3))
        topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][4,0][0][5],3))
        for count in range(0,int(columns)): 
            for count2 in range(0,int(rows)):
                #print("CHECK BODY WIDTH OF PMOS", wb, hb)
                oX, oY = count*(wp_eff+wb), 0 + count2*hp
                ref = gdspy.CellReference(cell, (oX, oY))          
                finY = oY
                #for count3 in range (1,4):   
                #    rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]), (oX+wp - (offset/2)-gap_offset/2 , finY+bottomFin2bottomBB - count3*layerSpecs["Fin"]["Pitch"]+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the MID PCELLs   (Vertical Space)
                #for count3 in range ( 4,8):   
                #    rectangles.append(gdspy.Rectangle((oX+(offset/2)-gap_offset/2, finY+hm+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wp - (offset/2)-gap_offset/2 , finY+hl+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the MID PCELLs   (Vertical Space)
                if gap_offset !=0:  #Only if the EG gap is not 0  
                    for count3 in range ( 0,22):   
                        rectangles.append(gdspy.Rectangle((oX+wp_eff-0.17, oY+(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wp_eff+gap_offset -0.17, oY+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the MID PCELLs   (Horizontal space)(right side)
                        rectangles.append(gdspy.Rectangle((oX-0.17, oY+(count3)*(layerSpecs['Fin']['Pitch'])), (oX +gap_offset-0.17 ,oY+(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap between the MID PCELLs   (Horizontal space)(left side)
                new_cell.add(ref)
    if ("BC_P" in cell.name) and mos_type != "N":
        #print("Instantiating the Body Contacts") 
        #bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][1],3))
        #topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][5],3)) 
        offsetl = 0.07 #Fil the gap between the BC and LEFT PCELLS
        offsetr = 2*round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2],3)  #offset for the right column of BCs
        blx=0
        for count in range(0,int(columns)): 
            for count2 in range(0,int(rows)):
                #print("\tInstantiating BC for left column")
                oX, oY = count*(wp_eff+wb) + wp_eff + offsetl, 0 + count2*hb
                #print("Instantiating",cell.name," at ",oX,",",oY)             
                #print(width, height)
                ref = gdspy.CellReference(cell, (oX, oY))   
                finY = oY
                    
                new_cell.add(ref)    
        
    if "BC" in cell.name and mos_type == "N":
        bottomFin2bottomBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'min','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][1],3))
        topFin2topBB = abs(round(find_extreme_coordinate(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42],'max','y')-all_polygon_coordinates[cell.name+".gds"][cell.name][3,0][0][5],3)) 
        offsetl = 0.06 #Fil the gap between the BC and LEFT PCELLS
        offsetr = 2*round(all_polygon_coordinates[cell.name+".gds"][cell.name][2,42][0][2],3)  #offset for the right column of BCs
        blx=0
        for count2 in range(0,int(rows)): 
            #print("\tInstantiating BC for left column")
            oX, oY = 0-wb/2 + offsetl , 0 + count2*hb
            blx=oX
            #print("Instantiating",cell.name," at ",oX,",",oY)             
            #print(width, height)
            ref = gdspy.CellReference(cell, (oX, oY))   
            finY = oY
            for count3 in range ( 1,4):   
                rectangles.append(gdspy.Rectangle((oX, finY+bottomFin2bottomBB -(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wb, finY+bottomFin2bottomBB -(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the BC PCELLs   (Vertical Space) at Left Column
            for count3 in range ( 4,8):   
                rectangles.append(gdspy.Rectangle((oX, finY+hb+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wb, finY+hb+topFin2topBB-(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the BC PCELLs   (Vertical Space)  at Left Column             
            new_cell.add(ref)    
        for count2 in range(0,int(rows)): 
            #print("\tInstantiating BC for right column")
            #oX, oY = wl-offset+(wm-offset)*(int(columns)-2) + wr , 0 + count2*hr
            #oX, oY = blx+wl+(wm)*(int(columns)-2)+wb - 2*offset, 0 + count2*hr
            oX, oY = wl_eff+wm_eff*(int(columns)-2)+wr_eff, 0 + count2*hr
            #print("Instantiating",cell.name," at ",oX,",",oY)             
            #print(width, height)
            ref = gdspy.CellReference(cell, (oX, oY))  
            finY = oY
            for count3 in range ( 1,4):   
                rectangles.append(gdspy.Rectangle((oX, finY+bottomFin2bottomBB -(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wb, finY+bottomFin2bottomBB -(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap below the BC PCELLs   (Vertical Space) at Left Column
            for count3 in range ( 4,8):   
                rectangles.append(gdspy.Rectangle((oX, finY+hb+topFin2topBB-(count3)*(layerSpecs['Fin']['Pitch'])), (oX+wb, finY+hb+topFin2topBB-(count3)*layerSpecs['Fin']['Pitch']+layerSpecs['Fin']['Width']), layer=2, datatype=42))  #Extra fins to fill the gap above the BC PCELLs   (Vertical Space)  at Left Column   
            new_cell.add(ref)   
 
translated_lib = gdspy.GdsLibrary(name = "Dummy",units = units)   
for cont in new_cells:        
    translated_lib.add(cont)
    
cell_arr = translated_lib.top_level()[0]
cell_arr.flatten()
polygons = cell_arr.get_polygons(True)  #Polygons
first_key, first_value = next(iter(polygons.items()))
#print(f'The first key-value pair is: {first_key}: {first_value}')
#print(list(polygons.keys()))
#print(polygons) #All the rectangles in the flattened layout
pincache = set()    
pindata = dict()  #Pin dictionary
bbox = cell_arr.get_bounding_box() / scale  #Boundary Box of the whole chip layout
#print("Initial Boundary Box: ",bbox)
jsondict = dict()
jsondict["bbox"] = [round(bbox[i][j]) for i in (0,1) for j in (0,1)]
jsondict["globalRoutes"] = []
jsondict["globalRouteGrid"] = []
jsondict["terminals"] = []
label_pos = list()
for lbl in cell_arr.get_labels():

    #print(lbl.text)
    #print(lbl.text) #Storing actual label ID (G,D,S)
    labellayer = (lbl.layer, lbl.texttype) #What layer and texttype (Label data type)
    #print(lbl.layer, lbl.texttype)
    if labellayer in labellayers:
        llayer = labellayers[labellayer]   
        #print(llayer) #Layer ID from layers.json
        lname = layernames[llayer] 
        #print(lname) #Layer name (say M1, M2, V0, etc)
        pos = lbl.position / scale    
        #print("HERE")
        #print(pos, lbl.text)
        label_pos.append((pos, lbl.text))
        #print(pos) #Position in the layout
        if lname in layers:
            pinindices = list()
            for idx, k in layers[lname].items():    #Looking for M1 in layers.json (layers) datatypes
                if k == 'Pin' or k == 'Draw':
                    pinindices.append(idx)
            #print(pinindices) #Gds data type ...say 0 for "Draw", 32 for "Pin"
            for pinidx in pinindices:
                key = (llayer, pinidx)  #(15, 20)
                #print(key)
                if key in polygons:
                    #print("Yes")
                    for poly in polygons[key]:
                        if len(poly) < 2: continue #Skip if its not atleast a rectangle (2 points LL an UR)
                        box = [round(min(r[0] for r in poly) / scale), round(min(r[1] for r in poly) / scale),
                               round(max(r[0] for r in poly) / scale), round(max(r[1] for r in poly) / scale)]  #Looking for min and max x and min and max y coordinates of the polygons for their bbox
                        #print(box) #All the polygons (Lower left and upper right)
                        #print("CEHCK")
                        #print(box, pos)
                        if box[0] <= pos[0] and box[1] <= pos[1] and box[2] >= pos[0] and box[3] >= pos[1]:
                            pindict = {"layer": lname, "netName": lbl.text, "rect": box, "netType": "pin"}
                            #print("Check",lbl.txt)
                            if lbl.text not in pindata:
                                pindata[lbl.text] = set()
                            pindata[lbl.text].add((lname, tuple(box)))
                            jsondict["terminals"].append(pindict)
                            pincache.add(str([key, box]))
            drawidx = None
            for idx, k in layers[lname].items():
                if k == 'Draw':
                    drawinidx = idx
                    break
            key = (llayer, drawinidx)
            if key in polygons:
                for poly in polygons[key]:
                    if len(poly) < 2: continue
                    box = [round(min(r[0] for r in poly) / scale), round(min(r[1] for r in poly) /scale),
                           round(max(r[0] for r in poly) / scale), round(max(r[1] for r in poly) / scale)]
                    if box[0] <= pos[0] and box[1] <= pos[1] and box[2] >= pos[0] and box[3] >= pos[1]:
                        pindict = {"layer": lname, "netName": lbl.text, "rect": box, "netType": "drawing"}
                        jsondict["terminals"].append(pindict)
                        pincache.add(str([key, box])) 

grouped_label_pos = dict()
#print(label_pos)
m4_pins = list()
for pair, name in label_pos:
    #print("PAIR and NAME:", pair, name)
    x_coord = pair[0]
    #Taking 1 x_coord at a time
    if x_coord not in grouped_label_pos:
        grouped_label_pos[x_coord] = {}
    g_pins = list() #List of GATE pins
    d_pins = list() #List of DRAIN pins
    s_pins = list() #List of SOURCE pins
    b_pins = list() #List of BODY pins
    for pair, name in label_pos: #Taking all y coordinates for different pins G, D, S for the given x_coord   
        #print(pair[0], x_coord)        
        if pair[0] == x_coord:
            pin = name
            if pin == 'G':
                g_pins.append(float(pair[1]))
            elif pin == 'D':
                d_pins.append(float(pair[1]))
            elif pin == 'S':
                s_pins.append(float(pair[1]))
            elif pin == 'B':
                b_pins.append(float(pair[1]))
    if 'G' in grouped_label_pos[x_coord]:
        for pin in g_pins:
            grouped_label_pos[x_coord]['G'].append(pin)
    else:
        grouped_label_pos[x_coord]['G']=g_pins

    if 'D' in grouped_label_pos[x_coord]:
        for pin in d_pins:
            grouped_label_pos[x_coord]['D'].append(pin)
    else:
        grouped_label_pos[x_coord]['D']=d_pins   
 
    if 'S' in grouped_label_pos[x_coord]:
        for pin in s_pins:
            grouped_label_pos[x_coord]['S'].append(pin)
    else:
        grouped_label_pos[x_coord]['S']=s_pins   
 
    if 'B' in grouped_label_pos[x_coord]:
        for pin in b_pins:
            grouped_label_pos[x_coord]['B'].append(pin)
    else:
        grouped_label_pos[x_coord]['B']=b_pins

#print(len(grouped_label_pos))
filtered_dict = grouped_label_pos.copy()
for k1,v1 in grouped_label_pos.items():  
    for k2, v2 in v1.items():  
        if k2 == "B" and len(v2)!=0:
            del(filtered_dict[k1])

#print(len(filtered_dict))
#sys.exit()
#print("PINS")
#print("G",g_pins,"D", d_pins,"S", s_pins,"B", b_pins)

def mid_level_routing():   
    def get_pos_index(grouped_dict, x): #Sorts the keys of a dict in increasing order and returns the index of any particular key in that dict
        sorted_keys = sorted(grouped_dict.keys())
        key_index = sorted_keys.index(x)
        return key_index

    def get_y_coordinate(column_index, pin, total_columns = columns, columns_per_block=5, place = placement):
        repeated_place = [item for item in place for _ in range(columns_per_block)]
        #print("get_y_coordinate")
        #print(repeated_place)
        #print(column_index)
        if mos_type =="N":
            a =1
        else:
            a =0
        if repeated_place[column_index-a] == 1:
            if pin =='D':
                return 1
            else:
                return 0
        else:
            if pin == 'D':
                return 0    
            else:
                return 1
    #print("Length",len(grouped_label_pos))
    for x,pin_lbls in grouped_label_pos.items():
        #print(x, pin_lbls)
        index = get_pos_index(grouped_label_pos, x) 
        x = x*scale
        #print("INDEX",index)
          
        for pin, lbls in pin_lbls.items():
            #print(pin)
            if mos_type =="N":
                grp = 5
            else:
                grp = 6
            if pin =='G':
                if lbls: 
                    #print(lbls)           
                    miny =100000000 
                    maxy=0
                    for ylbls in lbls:
                        ylbls = ylbls*scale
                        #print(ylbls)
                        if ylbls < miny:
                            miny = ylbls
                        if ylbls > maxy:
                            maxy = ylbls
                        #For lower GATE
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V1']['WidthX']/2, ylbls-layerSpecs['V1']['WidthY']/2), (x+layerSpecs['V1']['WidthX']/2, ylbls+layerSpecs['V1']['WidthY']/2), layer=16, datatype=0))        #V1 on M1  
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V1']['VencA_H']-layerSpecs['V1']['WidthX']/2, ylbls-m2_width/2), (x+layerSpecs['V1']['VencA_H']+layerSpecs['V1']['WidthX']/2, ylbls+m2_width/2), layer=17, datatype=0)) #M2 on V1
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V2']['WidthX']/2, ylbls-layerSpecs['V2']['WidthY']/2), (x+layerSpecs['V2']['WidthX']/2, ylbls+layerSpecs['V2']['WidthY']/2), layer=18, datatype=0))        #V2 on M2
                        if mos_type == "N":
                            gap_ngcon = abs(round(find_extreme_coordinate(all_polygon_coordinates["PCELL_LEFT.gds"]["PCELL_LEFT"][15,0],"max","y") -find_extreme_coordinate(all_polygon_coordinates["PCELL_LEFT.gds"]["PCELL_LEFT"][15,0],"min","y"),3)) - layerSpecs["M1"]["Width"] #Device parameter ngcon is the number of gate connects (Here 2) So 0.642 is the gap between the two GATE connects 
                        else:
                            gap_ngcon = abs(round(find_extreme_coordinate(all_polygon_coordinates["PMOS.gds"]["PMOS"][15,0],"max","y") -find_extreme_coordinate(all_polygon_coordinates["PMOS.gds"]["PMOS"][15,0],"min","y"),3)) - layerSpecs["M1"]["Width"] #Device parameter ngcon is the number of gate connects (Here 2) So 0.642 is the gap between the two GATE connects 
                        
                        #For upper GATE
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V1']['WidthX']/2, ylbls-layerSpecs['V1']['WidthY']/2+gap_ngcon), (x+layerSpecs['V1']['WidthX']/2, ylbls+layerSpecs['V1']['WidthY']/2+gap_ngcon), layer=16, datatype=0)) #V1 on M1
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V1']['VencA_H']-layerSpecs['V1']['WidthX']/2, ylbls-m2_width/2 + gap_ngcon), (x+layerSpecs['V1']['VencA_H']+layerSpecs['V1']['WidthX']/2, ylbls+m2_width/2 + gap_ngcon), layer=17, datatype=0)) #M2 on V1
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V2']['WidthX']/2, ylbls-layerSpecs['V2']['WidthY']/2+gap_ngcon), (x+layerSpecs['V2']['WidthX']/2, ylbls+layerSpecs['V2']['WidthY']/2+gap_ngcon), layer=18, datatype=0)) #V2 on M2
            

                    #HIGHER LEVEL ROUTING
                    if mos_type == "N":
                        miny = miny
                        maxy=rows*hl+layerSpecs['M4']['Pitch'] +m4_width #For gate metal layers from PCELL (top and bottom)
                    else:
                        miny = -layerSpecs['M4']['Pitch']-m4_width
                        maxy = maxy + gap_ngcon- layerSpecs["M1"]["Width"]#For gate metal layers from PCELL (top and bottom)
                    max_x = max(grouped_label_pos.keys())*scale
                    min_x = min(grouped_label_pos.keys())*scale
                    m4_pins.append([x, min_x, miny, max_x, maxy,'G'])
                        
                    
            elif pin == 'D':
                if lbls: 
                    #print(lbls)           
                    miny =100000000 
                    maxy=0
                    for ylbls in lbls:
                        ylbls = ylbls*scale
                        #print(ylbls)
                        if ylbls < miny:
                            miny = ylbls
                        if ylbls > maxy:
                            maxy = ylbls
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V2']['WidthX']/2, ylbls-layerSpecs['V2']['WidthY']/2), (x+layerSpecs['V2']['WidthX']/2, ylbls+layerSpecs['V2']['WidthY']/2), layer=18, datatype=0))    #V2 on M2
                    
                    y = get_y_coordinate(index,'D', columns, grp)
                    if y==0:
                        
                        if mos_type == "N":
                            miny=miny
                            maxy=rows*hl +2*layerSpecs['M4']['Pitch']+2*m4_width #For drain metal layers from PCELL (top and bottom)
                        else:
                            miny = 2*(-layerSpecs['M4']['Pitch']-m4_width)
                            maxy = maxy
                            #maxy = rows*hp +2*layerSpecs['M4']['Pitch']+2*m4_width #For drain metal layers from PCELL (top and bottom)
                    elif y==1:
                        
                        if mos_type == "N":
                            miny = miny
                            maxy = rows*hl +3*layerSpecs['M4']['Pitch']+3*m4_width#For drain metal layers from PCELL (top and bottom)
                        else:
                            miny = 3*(-layerSpecs['M4']['Pitch']-m4_width)
                            maxy = maxy
                            #maxy = rows*hp +3*layerSpecs['M4']['Pitch']+3*m4_width#For drain metal layers from PCELL (top and bottom)
                
                    max_x = max(grouped_label_pos.keys())*scale
                    min_x = min(grouped_label_pos.keys())*scale
                    m4_pins.append([x, min_x, miny, max_x, maxy,'D'])

            elif pin == 'S':
                if lbls: 
                    #print(lbls)           
                    miny =100000000 
                    maxy=0
                    for ylbls in lbls:
                        ylbls = ylbls*scale
                        #print(ylbls)
                        if ylbls < miny:
                            miny = ylbls
                        if ylbls > maxy:
                            maxy = ylbls
                        rectangles.append(gdspy.Rectangle((x-layerSpecs['V2']['WidthX']/2, ylbls-layerSpecs['V2']['WidthY']/2), (x+layerSpecs['V2']['WidthX']/2, ylbls+layerSpecs['V2']['WidthY']/2), layer=18, datatype=0))    #V2 on M2
                   
                    y = get_y_coordinate(index,'S', columns, grp)
                    if y==1:
                        if mos_type == "N":
                            miny=-layerSpecs['M4']['Pitch']-m4_width #For source metal layers from PCELL (top and bottom)
                            maxy=maxy 
                        else:   
                            miny=miny #For source metal layers from PCELL (top and bottom)
                            maxy=rows*hp + layerSpecs['M4']['Pitch']+ m4_width
                    else:
                        if mos_type == "N":
                            miny=-2*layerSpecs['M4']['Pitch']-2*m4_width #- 6*layerSpecs['M4']['Pitch'] #For source metal layers from PCELL (top and bottom)
                            maxy=maxy
                        else:
                            miny=miny #For source metal layers from PCELL (top and bottom)
                            maxy=rows*hp +2*(layerSpecs['M4']['Pitch']+m4_width)
             
                    max_x = max(grouped_label_pos.keys())*scale
                    min_x = min(grouped_label_pos.keys())*scale
                    m4_pins.append([x, min_x, miny, max_x, maxy, 'S'])
                    
            elif pin == 'B':
                if lbls: 
                    #print(lbls)           
                    miny =100000000 
                    maxy=0
                    lbls = list(dict.fromkeys(lbls)) #Removing duplicates
                    for ylbls in lbls:
                        ylbls = ylbls*scale
                        print(ylbls)
                        if ylbls < miny:
                            miny = ylbls
                        if ylbls > maxy:
                            maxy = ylbls
                        if mos_type == "P":
                            l_m1 = find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'max','x') - find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'min','x') 
                            w_m1 = find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'max','y') - find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'min','y')
                        else:
                            l_m1 = find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'max','x') - find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'min','x') 
                            w_m1 = find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'max','y') - find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'min','y') 
                        rectangles.append(gdspy.Rectangle((x-l_m1/2 + layerSpecs['V1']['WidthX']/2, ylbls-w_m1/2 + layerSpecs['V1']['WidthX']/2), (x+l_m1/2 - layerSpecs['V1']['WidthX']/2, ylbls+w_m1/2 - layerSpecs['V1']['WidthX']/2), layer=17, datatype=0)) #M2 on V1
                        if source_body == 1:
                            m_gap = find_extreme_coordinate(all_polygon_coordinates["PMOS.gds"]["PMOS"][2,42],'max','x') - find_extreme_coordinate(all_polygon_coordinates["PMOS.gds"]["PMOS"][17,0],'max','x') 
                            b_gap = find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'min','x') - find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][2,42],'min','x')
                            m2_gap = m_gap + b_gap 
                            rectangles.append(gdspy.Rectangle((x-m2_gap-l_m1/2 - 0.05 -gap_offset, ylbls+w_m1/2 - 0.085), (x-l_m1/2 + 0.05, ylbls+w_m1/2 - layerSpecs['V1']['WidthX']/2), layer=17, datatype=0)) #M2 connecting SOURCE and BODY

                        #rectangles.append(gdspy.Rectangle((x-layerSpecs['V1']['VencA_H']-layerSpecs['V1']['WidthX']/2, ylbls-layerSpecs['V1']['WidthY']/2), (x+layerSpecs['V1']['VencA_H']+layerSpecs['V1']['WidthX']/2, ylbls+layerSpecs['V1']['WidthY']/2), layer=17, datatype=0)) #M2 on V1
                        if mos_type == "N":
                            m2_gap = find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'max','y') - find_extreme_coordinate(all_polygon_coordinates["BC_N.gds"]["BC_N"][15,0],'min','y')
                        else:
                            m2_gap = find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'max','y') - find_extreme_coordinate(all_polygon_coordinates["BC_P.gds"]["BC_P"][15,0],'min','y')
                        createVia('M1',w_m1,16,'V1','M2',w_m1 ,x,ylbls-w_m1/2) 
                        if source_body != 1:   
                            createVia('M2',m3_width,18,'V2','M3',l_m1,x,ylbls-l_m1/2)                        
                        #rectangles.append(gdspy.Rectangle((x-layerSpecs['V2']['WidthX']/2, ylbls-layerSpecs['V2']['WidthY']/2), (x+layerSpecs['V2']['WidthX']/2, ylbls+layerSpecs['V2']['WidthY']/2), layer=18, datatype=0))        #V2 on M2

                    if mos_type == "N":
                        miny=-3*layerSpecs['M4']['Pitch']-3*m4_width  #For body metal layers from PCELL (top and bottom)
                        maxy=maxy 
                    else:
                        miny=miny
                        maxy=rows*hp + 3* (layerSpecs['M4']['Pitch'] + m4_width)
                    max_x = max(grouped_label_pos.keys())*scale
                    min_x = min(grouped_label_pos.keys())*scale
                    m4_pins.append([x, min_x, miny, max_x, maxy, 'B'])
       
# Add the rectangle to the cell
def createVia(lm_name,lm_width,viaid, via_name, um_name, um_width, cenx, ceny):
    #print(ceny)
    ceny = ceny+um_width/2
    #print("Inserting via",via_name," at cenx and ceny ", cenx, ceny)
    area = lm_width * um_width          #Area of intersection to be filled with maximum number of VIAs
    #print(lm_name, um_name)
    dir_lm = layerSpecs[lm_name]['Direction']
    dir_um = layerSpecs[um_name]['Direction']
    if dir_lm == "H":
        x_red = layerSpecs[via_name]['VencP_H'] 
        y_red = layerSpecs[via_name]['VencP_L']
    else:   
        x_red = layerSpecs[via_name]['VencP_L'] 
        y_red = layerSpecs[via_name]['VencP_H']
    
    eff_l = lm_width - x_red - layerSpecs[via_name]["WidthX"]/2
    eff_w = um_width - y_red - layerSpecs[via_name]["WidthY"]/2
    #print("Effective length and width ", eff_l,eff_w)
    minx = cenx - eff_l/2
    miny = ceny - eff_w/2
    maxx = cenx + eff_l/2
    maxy = ceny + eff_w/2
    x = cenx
    while x <= maxx:
        y = ceny
        while y <=maxy:
            rectangles.append(gdspy.Rectangle((x-layerSpecs[via_name]['WidthX']/2, y - layerSpecs[via_name]['WidthY']/2), (x+layerSpecs[via_name]['WidthX']/2, y + layerSpecs[via_name]['WidthY']/2), layer=viaid, datatype=0)) #V3 on M3
            y = y + layerSpecs[via_name]['WidthY'] + layerSpecs[via_name]['SpaceY'] 
        y = ceny - layerSpecs[via_name]['WidthY'] - layerSpecs[via_name]['SpaceY'] 
        while y >=miny:
            rectangles.append(gdspy.Rectangle((x-layerSpecs[via_name]['WidthX']/2, y - layerSpecs[via_name]['WidthY']/2), (x+layerSpecs[via_name]['WidthX']/2, y + layerSpecs[via_name]['WidthY']/2), layer=viaid, datatype=0)) #V3 on M3
            y = y - layerSpecs[via_name]['WidthY'] - layerSpecs[via_name]['SpaceY'] 

        x = x + layerSpecs[via_name]['WidthX'] + layerSpecs[via_name]['SpaceX']
    x = cenx - layerSpecs[via_name]['WidthX'] - layerSpecs[via_name]['SpaceX']
    while x >= minx:
        y = ceny
        while y <=maxy:
            rectangles.append(gdspy.Rectangle((x-layerSpecs[via_name]['WidthX']/2, y - layerSpecs[via_name]['WidthY']/2), (x+layerSpecs[via_name]['WidthX']/2, y + layerSpecs[via_name]['WidthY']/2), layer=viaid, datatype=0)) #V3 on M3
            y = y + layerSpecs[via_name]['WidthY'] + layerSpecs[via_name]['SpaceY'] 
        y = ceny - layerSpecs[via_name]['WidthY'] - layerSpecs[via_name]['SpaceY'] 
        while y >=miny:
            rectangles.append(gdspy.Rectangle((x-layerSpecs[via_name]['WidthX']/2, y - layerSpecs[via_name]['WidthY']/2), (x+layerSpecs[via_name]['WidthX']/2, y + layerSpecs[via_name]['WidthY']/2), layer=viaid, datatype=0)) #V3 on M3
            y = y - layerSpecs[via_name]['WidthY'] - layerSpecs[via_name]['SpaceY'] 

        x = x - layerSpecs[via_name]['WidthX'] - layerSpecs[via_name]['SpaceX']


def high_level_routing():
    old_maxygn=list() #Max for top horizontal layers
    old_maxydn=list() 
    old_minysn=list() #Min for bottom horizontal layers
    old_minybn=list()
    
    old_minygp=list() #Max for top horizontal layers
    old_minydp=list() 
    old_maxysp=list() #Min for bottom horizontal layers
    old_maxybp=list()
        
    for pins in m4_pins:
        #print("\n",pins)    
        x = pins[0]
        min_x = pins[1]
        miny = pins[2]
        max_x = pins[3]
        maxy = pins[4]
        #FOR NMOS D and G are on TOP, S and B are at bottom and vice versa for PMOS
        if mos_type == "N":
            if pins [-1] == 'G':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny-layerSpecs['V3']['VencA_H']-m4_width/2), (x+m3_width/2, maxy +m4_width + layerSpecs['V3']['WidthY']/2 +layerSpecs['V3']['VencA_H'] ), layer=19, datatype=0))  #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,maxy)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3 
                if maxy not in old_maxygn:
                    old_maxygn.append(maxy)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, maxy), (max_x+m3_width/2, maxy+m4_width), layer=41, datatype=0)) #M4 on V3
            elif pins[-1] == 'B':
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny -layerSpecs['V3']['WidthY']/2 - layerSpecs['V3']['VencA_L']), (x+m3_width/2, maxy+layerSpecs['V1']['VencA_H']+m4_width/2), layer=19, datatype=0)) #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,miny)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, miny+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, miny+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                if miny not in old_minybn:
                    old_minybn.append(miny)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2 - layerSpecs['V3']['VencA_H'], miny), (max_x+m3_width/2 +layerSpecs['V3']['VencA_H'], miny+m4_width), layer=41, datatype=0)) #M4 on V3
            elif pins[-1] == 'S':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny  - layerSpecs['V3']['WidthY']/2 - layerSpecs['V3']['VencA_L']), (x+m3_width/2, maxy+layerSpecs['V2']['VencA_H']+m4_width/2 ), layer=19, datatype=0)) #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,miny)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, miny+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, miny+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                if miny not in old_minysn:
                    old_minysn.append(miny)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, miny), (max_x+m3_width/2, miny+m4_width), layer=41, datatype=0)) #M4 on V3
            elif pins[-1]=='D':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny-layerSpecs['V2']['VencA_H']-m4_width/2), (x+m3_width/2, maxy+layerSpecs['V3']['VencA_H']+layerSpecs['V3']['WidthY']/2 + m4_width), layer=19, datatype=0))  #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,maxy)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                if maxy not in old_maxydn:
                    old_maxydn.append(maxy)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, maxy), (max_x+m3_width/2, maxy+m4_width), layer=41, datatype=0)) #M4 on V3
        elif mos_type =="P":
            if pins [-1] == 'G':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny-layerSpecs['V3']['VencA_H']-m4_width/2), (x+m3_width/2, maxy +m4_width/2 + layerSpecs['V3']['WidthY']/2 +layerSpecs['V3']['VencA_H'] ), layer=19, datatype=0))  #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,miny)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, miny+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, miny+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3 
                if miny not in old_minygp:
                    old_minygp.append(miny)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, miny), (max_x+m3_width/2, miny+m4_width), layer=41, datatype=0)) #M4 on V3
            elif pins[-1] == 'B':
                if source_body != 1:
                    rectangles.append(gdspy.Rectangle((x-m3_width/2, miny -layerSpecs['V3']['WidthY']/2 - layerSpecs['V3']['VencA_L']), (x+m3_width/2, maxy+layerSpecs['V1']['VencA_H']+m4_width), layer=19, datatype=0)) #M3 on V2
                    createVia('M3',m3_width,61,'V3','M4',m4_width,x,maxy)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                    if maxy not in old_maxybp:
                        old_maxybp.append(maxy)
                        rectangles.append(gdspy.Rectangle((min_x-m3_width/2 - layerSpecs['V3']['VencA_H'], maxy), (max_x+m3_width/2 +layerSpecs['V3']['VencA_H'], maxy+m4_width), layer=41, datatype=0)) #M4 on V3

            elif pins[-1] == 'S':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny  - layerSpecs['V3']['WidthY']/2 - layerSpecs['V3']['VencA_L']), (x+m3_width/2, maxy+layerSpecs['V2']['VencA_H']+m4_width ), layer=19, datatype=0)) #M3 on V2
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,maxy)
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, maxy+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                if maxy not in old_maxysp:
                    old_maxysp.append(maxy)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, maxy), (max_x+m3_width/2, maxy+m4_width), layer=41, datatype=0)) #M4 on V3
            elif pins[-1]=='D':
                #print(pins)
                rectangles.append(gdspy.Rectangle((x-m3_width/2, miny-layerSpecs['V2']['VencA_H']-m4_width/2), (x+m3_width/2, maxy+layerSpecs['V3']['VencA_H']+layerSpecs['V3']['WidthY']/2 + m4_width/2), layer=19, datatype=0))  #M3 on V2
                #rectangles.append(gdspy.Rectangle((x-layerSpecs['V3']['WidthX']/2, miny+m4_width/2 - layerSpecs['V3']['WidthY']/2), (x+layerSpecs['V3']['WidthX']/2, miny+m4_width/2 + layerSpecs['V3']['WidthY']/2), layer=61, datatype=0)) #V3 on M3
                createVia('M3',m3_width,61,'V3','M4',m4_width,x,miny)
                if miny not in old_minydp:
                    old_minydp.append(miny)
                    rectangles.append(gdspy.Rectangle((min_x-m3_width/2, miny), (max_x+m3_width/2, miny+m4_width), layer=41, datatype=0)) #M4 on V3
            
if mid_rout == 1:            
    mid_level_routing()  
    #print("M4_PINS",m4_pins, len(m4_pins))    
if high_rout == 1:
    high_level_routing()
        
for rect in rectangles:
    cell_arr.add(rect)
    


def add_boundary_layers():
    boundary_box_rect = list()
    min_x = float('inf')
    max_x = float('-inf')
    min_y = float('inf')
    max_y = float('-inf')
    for rect in rectangles:
        (x_min, y_min), (x_max, y_max) = rect.get_bounding_box()
        min_x = min(min_x, x_min)
        max_x = max(max_x, x_max)
        min_y = min(min_y, y_min)
        max_y = max(max_y, y_max)
    boundary_box_rect.append(gdspy.Rectangle((min_x - 1.35, min_y - 0.3), (max_x + 0.3, max_y+0.3), layer=62, datatype=1))
    boundary_box_rect.append(gdspy.Rectangle((min_x - 1.4, min_y - 0.35), (max_x + 0.35, max_y+0.35), layer=62, datatype=21))
    for rects in boundary_box_rect:
        cell_arr.add(rects)



add_boundary_layers()

output_gds_file = "combined_1st.gds"
translated_lib.write_gds(output_gds_file)
print(f'Layout generated at {output_gds_file}')
##LINE 1

#print(layerSpecs['V1']['VencA_H'])
#print(f'writing gds file {top_cell}_out.gds')
#gdslib.write_gds(top_cell + '_out.gds')
