import numpy as np
import sys
import matplotlib.pyplot as plt


def readfile(filename):
  matrix = []
  with open(filename, 'r') as file_to_read:
    while True:
      lines = file_to_read.readline()
      if not lines:
        break
      p_tmp = [int(i) for i in lines.split()]
      matrix.append(p_tmp)
  matrix = np.array(matrix)
  return matrix

def metal_via_data(matrix,layer):
  temp_matrix = []
  for i in range(matrix.shape[0]):
    if(matrix[i][4]==layer):
      temp_matrix.append(matrix[i].tolist())
  temp_matrix = np.array(temp_matrix)
  return temp_matrix

def plot_grid_metal_via(temp_matrix,layer):
  internal_metal = []
  via = []
  MetalOfVia = []
  for i in range(temp_matrix.shape[0]):
    if(temp_matrix[i][5]==1):
      internal_metal.append(temp_matrix[i])
    if(temp_matrix[i][5]==2):
      via.append(temp_matrix[i])
    if(temp_matrix[i][5]==3):
      MetalOfVia.append(temp_matrix[i])
  plot_Box(internal_metal,'b')
  plot_Box(via,'r')
  plot_Box(MetalOfVia,'g')
  plt.savefig(str(layer)+"_MetalVias.png")
  plt.show()

def plot_Box(temp_matrix,c):
    for ele in temp_matrix:
        plot_box(ele[0],ele[1],ele[2],ele[3],c)

def plot_box(llx,lly,urx,ury,c):
    plt.plot([llx,urx], [lly,lly], lw=2, color=c)
    plt.plot([urx,urx], [lly,ury], lw=2, color=c)
    plt.plot([urx,llx], [ury,ury], lw=2, color=c)
    plt.plot([llx,llx], [lly,ury], lw=2, color=c)
  

filename_metalvia = sys.argv[1] 
layer = int(sys.argv[2])
matrix = readfile(filename_metalvia)
temp_matrix = metal_via_data(matrix,layer)
plot_grid_metal_via(temp_matrix,layer)
