from gstools import SRF, Gaussian
import matplotlib.pyplot as plt
import numpy as np

from itertools import product

# structured field with a size 40x40 and a grid-size of 1x1
delta = 1/20
x = y = np.arange( -1, 1 + delta/2, delta)

fig = plt.figure()

n = m = 4

scale = 4 # or 1 or 5

for (r,c) in product( range(n), range(m)):

    ax = fig.add_subplot( n,m, r*m+c+1)
    model = Gaussian(dim=2, var=1, len_scale=scale)
    srf = SRF(model)
    field = srf((x, y), mesh_type='structured')
    ax.contour(x,y,field)

plt.show()
