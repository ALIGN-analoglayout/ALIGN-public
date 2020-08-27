import json
import sys

#1. extend entire boundry
def find_max(xy):
  max_y = xy[3]
  max_x = xy[4]
  return max_x, max_y

def extend(xy, extend_x, extend_y):
  max_y  = 0
  max_x = 0
  xy[0] = xy[0]
  xy[1] = xy[1]
  xy[2] = xy[2]
  max_y = xy[3]
  xy[3] = xy[3] + extend_y
  max_x = xy[4]
  xy[4] = xy[4] + extend_x
  xy[5] = xy[5] + extend_y
  xy[6] = xy[6] + extend_x
  xy[7] = xy[7]
  xy[8] = xy[8]
  xy[9] = xy[9]
  return max_x, max_y

#2. add some layer
def add_certain_layer(type_name, layer_nubmer, datatype, x, y, w, h):
  element={}
  xy=[]
  element["type"] = type_name
  element["layer"] = layer_nubmer
  element["datatype"] = datatype
  xy.append(int(x))
  xy.append(int(y))
  xy.append(int(x))
  xy.append(int(y+h))
  xy.append(int(x+w))
  xy.append(int(y+h))
  xy.append(int(x+w))
  xy.append(int(y))
  xy.append(int(x))
  xy.append(int(y))
  element["xy"] = xy
  return element


unit_scale_gds = 4 # from layer.json to gds, 1nm to 2.5e-10m, 1nm/2.5e-10m
unit_scale_verlog = 4000 # from gds to verilog, 2.5e-10m to 1um, 1um/2.5e-10m

target_cell = sys.argv[1]
file_name = target_cell + ".gds.json"
write_file_name = target_cell + "_tapcell.gds.json"

with open(file_name, "r") as read_file:
    data = json.load(read_file)

bgnstr = data["bgnlib"][0]["bgnstr"]
p_m2 = 54 * unit_scale_gds
w_m2 = 18 * unit_scale_gds

max_x = 0
max_y = 0
extend_x = 0
extend_y = 2*p_m2 # 2 times of m2 pitches

x = 0
y = 0
w = 0
h = 0

for i in range(len(bgnstr)):
  # find target_cell
  if bgnstr[i]["strname"] == target_cell:
    # extend boundry and nwell
    for j in range(len(bgnstr[i]["elements"])):
      # extend boundry 
      #print(bgnstr[i]["elements"][j].keys())
      #print(bgnstr[i]["elements"][j])
      if(not bgnstr[i]["elements"][j].__contains__("layer")):
        continue
      if bgnstr[i]["elements"][j]["layer"] == 12 or bgnstr[i]["elements"][j]["layer"] == 13:
         max_x, max_y = find_max(bgnstr[i]["elements"][j]["xy"])
      # extend nwell 
      if bgnstr[i]["elements"][j]["layer"] == 1:
         max_x, max_y = extend(bgnstr[i]["elements"][j]["xy"], extend_x, extend_y)
    # add active

    x = 0
    y = max_y + p_m2 - 0.5*w_m2
    w = max_x
    h = w_m2

    active_ele = add_certain_layer("boundary", 11, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(active_ele)
    # add LISD
    lisd_ele = add_certain_layer("boundary", 17, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(lisd_ele)
    # add v0
    v0_ele = add_certain_layer("boundary", 18, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(v0_ele)
    # add M1
    m1_ele = add_certain_layer("boundary", 19, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(m1_ele)
    # add V1
    v1_ele = add_certain_layer("boundary", 21, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(v1_ele)
    # add M2
    m2_ele = add_certain_layer("boundary", 20, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(m2_ele)
    # add SDT
    sdt_ele = add_certain_layer("boundary", 88, 0, x, y, w, h) #0 drawing, x= 0 , y = max_y + pitch of m2 , w = w of the boundry, h = m2 width
    #bgnstr[i]["elements"].append(sdt_ele)

    index = 0
    for j in range(len(bgnstr[i]["elements"])):
      if bgnstr[i]["elements"][j]["type"]=="sref":
        index = j
        break

    bgnstr[i]["elements"].insert(index,active_ele)
    index = index + 1
    
    bgnstr[i]["elements"].insert(index,lisd_ele)
    index = index + 1

    bgnstr[i]["elements"].insert(index,v0_ele)
    index = index + 1

    bgnstr[i]["elements"].insert(index,m1_ele)
    index = index + 1

    bgnstr[i]["elements"].insert(index,v1_ele)
    index = index + 1

    bgnstr[i]["elements"].insert(index,m2_ele)
    index = index + 1

    bgnstr[i]["elements"].insert(index,sdt_ele)
    index = index + 1 

   
new_json = json.dumps(data, indent = 4)

#with open("new.json",'w', encoding='utf-8') as f:
with open(write_file_name,'w') as f:
  f.write(new_json)

print("Change the boundry of ", target_cell, "in lef file, boundry ", 0, 0, max_x/unit_scale_verlog, (max_y + 2*p_m2)/unit_scale_verlog)
print("Add M2 pin Bg for ", target_cell, "in lef file, boundry ", x/unit_scale_verlog, y/unit_scale_verlog, (x+w)/unit_scale_verlog, (y+h)/unit_scale_verlog )
print("Add block M1 for ", target_cell, "in lef file, boundry ", x/unit_scale_verlog, y/unit_scale_verlog, (x+w)/unit_scale_verlog, (y+h)/unit_scale_verlog )
print("Add pin Bg in verilog file for ", target_cell)



