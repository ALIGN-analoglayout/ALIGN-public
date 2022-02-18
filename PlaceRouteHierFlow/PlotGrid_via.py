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

def grid_data_via(matrix,layer):
  temp_matrix = []
  for i in range(matrix.shape[0]):
    if(matrix[i][2]==layer):
      temp_matrix.append(matrix[i].tolist())
  temp_matrix = np.array(temp_matrix)
  return temp_matrix

def plot_grid_via(temp_matrix,layer):
  x_all = []
  y_all = []
  x_down = []
  y_down = []
  x_up = []
  y_up = []
  for i in range(temp_matrix.shape[0]):
    if(temp_matrix[i][3]==1):
      x_all.append(temp_matrix[i][0])
      y_all.append(temp_matrix[i][1])
    if(temp_matrix[i][3]==2):
      x_down.append(temp_matrix[i][0])
      y_down.append(temp_matrix[i][1])
    if(temp_matrix[i][3]==3):
      x_up.append(temp_matrix[i][0])
      y_up.append(temp_matrix[i][1])
  plt.plot(x_all,y_all,'g.',label='via up and down')
  plt.plot(x_down,y_down,'r.',label='via down')
  plt.plot(x_up,y_up,'b.',label='via up')
  plt.legend()
  plt.savefig(str(layer)+"via_.png")
  plt.show()
  

filename = sys.argv[1] 
layer = int(sys.argv[2])
matrix = readfile(filename)
temp_matrix = grid_data_via(matrix,layer)
plot_grid_via(temp_matrix,layer)



