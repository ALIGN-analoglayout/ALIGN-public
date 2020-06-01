#from mpl_toolkits.mplot3d import axes3d
import matplotlib.pyplot as plt
import matplotlib
from matplotlib import cm
import numpy as np
import math
#matplotlib.use('WXAgg')

filename = 'gridresult.txt' 
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

metal1 = 7
metal2 = 8
power = 0

print(data.shape)
X1 = []
Y1 = []
X2 = []
Y2 = []
X3 = []
Y3 = []
Z = []
x = []
y = []
z = []

for i in(range(data.shape[0])):
  if data[i][2] == metal1 and data[i][3] == power and data[i][6] == metal1 and data[i][7] == power:
     X1.append([data[i][0],data[i][4]])
     Y1.append([data[i][1],data[i][5]])
     #X2.append(data[i][4])
     #Y2.append(data[i][5])
     if data[i][0] not in x:
       x.append(data[i][0])
     if data[i][1] not in y:
       y.append(data[i][1])
  if data[i][2] == metal2 and data[i][3] == power and data[i][6] == metal2 and data[i][7] == power:
     X2.append([data[i][0],data[i][4]])
     Y2.append([data[i][1],data[i][5]])
  if data[i][0] == data[i][4] and data[i][3] == power and data[i][5] == data[i][1] and data[i][7] == power:
     if (data[i][2] == metal1 and data[i][6] == metal2) or (data[i][2] == metal2 and data[i][6] == metal1):     
        X3.append(data[i][0])
        Y3.append(data[i][1])

X1 = np.array(X1)
Y1 = np.array(Y1)
X2 = np.array(X2)
Y2 = np.array(Y2)
X3 = np.array(X3)
Y3 = np.array(Y3)


#print(X1)
#plt.plot(data1[:,0], data1[:,2],  color='skyblue', label='y1')
#plt.plot(data2[:,0], data2[:,3], color='blue', label='y2')

for i in range(len(X1)):
  plt.plot(X1[i], Y1[i], color='r')
  #plt.scatter(X1[i], Y1[i], color='b')
for i in range(len(X2)):
  plt.plot(X2[i], Y2[i], color='green')
  #plt.scatter(X2[i], Y2[i], color='black')
for i in range(len(X3)):
  plt.scatter(X3[i], Y3[i], color='brown', marker = 's')
'''
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
''' 
plt.show()

