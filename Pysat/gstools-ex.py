from gstools import SRF, Gaussian
import matplotlib.pyplot as plt
import numpy as np

from itertools import product

# structured field with a size 100x100 and a grid-size of 1x1
x = y = np.arange(-1,1.005,0.01)

fig = plt.figure()

n = m = 4

scale = 20 # or 1 or 5

for (r,c) in product( list(range(n)), list(range(m))):

    ax = fig.add_subplot( n,m, r*m+c+1)
    model = Gaussian(dim=2, var=1, len_scale=scale)
    srf = SRF(model)
    field = srf((x, y), mesh_type='structured')
    ax.contour(x,y,field)

plt.show()
