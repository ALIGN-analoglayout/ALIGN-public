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
      p_tmp = [float(i) for i in lines.split()]
      matrix.append(p_tmp)
  matrix = np.array(matrix)
  return matrix

def grid_data(matrix,layer):
  temp_matrix = []
  for i in range(matrix.shape[0]):
    if(matrix[i][2]==layer):
      print('find ',layer)
      temp_matrix.append(matrix[i].tolist())
  temp_matrix = np.array(temp_matrix)
  return temp_matrix

def plot_grid(temp_matrix):
  print(temp_matrix.shape)
  vdd_x = []
  vdd_y = []
  gnd_x = []
  gnd_y = []
  for i in range(temp_matrix.shape[0]):
    if temp_matrix[i][4]!=0:
      vdd_x.append(temp_matrix[i][0])
      vdd_y.append(temp_matrix[i][1])
    else:
      gnd_x.append(temp_matrix[i][0])
      gnd_y.append(temp_matrix[i][1])
  print(len(vdd_x))
  print(len(gnd_x))
  plt.plot(vdd_x,vdd_y,'r.')
  plt.plot(gnd_x,gnd_y,'b.')
  plt.savefig("filename.png")
  plt.show()
  

filename = sys.argv[1] 
layer = int(sys.argv[2])
matrix = readfile(filename)
temp_matrix = grid_data(matrix,layer)
plot_grid(temp_matrix)



