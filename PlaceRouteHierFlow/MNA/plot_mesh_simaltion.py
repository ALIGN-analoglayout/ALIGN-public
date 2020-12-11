from mpl_toolkits.mplot3d import axes3d
import matplotlib.pyplot as plt
import matplotlib
from matplotlib import cm
import numpy as np
import math
#matplotlib.use('WXAgg')

filename = 'Powergridresult.txt' 
data = []

with open(filename, 'r') as file_to_read:
  while True:
    lines = file_to_read.readline() 
    if not lines:
      break
      pass
    lines = [float(i) for i in lines.split()]
    data.append(lines)  # 添加新读取的数据
    pass
  data = np.array(data) # 将数据从list类型转换为array类型。
   
print(data)

metal = 5
power = 1

print(data.shape)
X = []
Y = []
Z = []
x = []
y = []
z = []

for i in(range(data.shape[0])):
  if data[i][2] == metal and  data[i][4] == power:
     X.append(data[i][0])
     Y.append(data[i][1])
     Z.append(data[i][3])
     if data[i][0] not in x:
       x.append(data[i][0])
     if data[i][1] not in y:
       y.append(data[i][1])

X = np.array(X)
Y = np.array(Y)
Z = np.array(Z)    
fig = plt.figure()
ax = fig.gca(projection='3d')
#X, Y, Z = axes3d.get_test_data(0.05)
line_x = np.array(x)
line_y  = np.array(y)

Xmesh, Ymesh = np.meshgrid(line_x, line_y)
print(Xmesh)
print(Ymesh)

z = np.zeros(Xmesh.shape)

for i in(range(line_x.shape[0])):
  for j in(range(line_y.shape[0])):
    for k in(range(X.shape[0])):
      if X[k]==line_x[i] and Y[k]==line_y[j]:
        z[j][i]=Z[k]

print(z)

#Z  = Z.reshape((math.floor(Z.shape[0]/1),1))

#print('x', X.dtype)
#print('x length', X.shape)
#print('x[0] length', X[0].shape)
#print(X)

#print('y', Y.dtype)
#print(Y)

#print('Z', Z.dtype)
#print(Z)

ax.plot_surface(Xmesh, Ymesh, z, rstride=1, cstride=1)
cset = ax.contour(Xmesh, Ymesh, z, zdir='z', offset=0.5, cmap=cm.rainbow)
#cset = ax.contour(X, Y, Z, zdir='x', offset=-40, cmap=cm.coolwarm)
#cset = ax.contour(X, Y, Z, zdir='y', offset=40, cmap=cm.coolwarm)
 
ax.set_xlabel('X')
ax.set_xlim(0, 11000)
ax.set_ylabel('Y')
ax.set_ylim(0, 11000)
ax.set_zlabel('Z')
ax.set_zlim(0.5, 1)
fig.savefig('demo.png', bbox_inches='tight')
 
plt.show()

