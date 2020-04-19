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

def grid_data(matrix,layer):
  temp_matrix = []
  for i in range(matrix.shape[0]):
    if(matrix[i][2]==matrix[i][5] and matrix[i][2]==layer):
      temp_matrix.append(matrix[i].tolist())
  temp_matrix = np.array(temp_matrix)
  return temp_matrix

def plot_grid(temp_matrix):
  x = []
  y = []
  sdx = []
  sdy = []
  for i in range(temp_matrix.shape[0]):
    x.append(temp_matrix[i][0])
    x.append(temp_matrix[i][3])
    y.append(temp_matrix[i][1])
    y.append(temp_matrix[i][4])
    if(temp_matrix[i][0] == temp_matrix[i][3] and temp_matrix[i][1]==temp_matrix[i][4] ):
      sdx.append(temp_matrix[i][0])
      sdy.append(temp_matrix[i][1])
  plt.plot(x,y,'b.')
  plt.plot(sdx,sdy,'r.')
  plt.savefig("filename.png")
  plt.show()
  

filename = sys.argv[1] 
layer = int(sys.argv[2])
matrix = readfile(filename)
temp_matrix = grid_data(matrix,layer)
plot_grid(temp_matrix)



