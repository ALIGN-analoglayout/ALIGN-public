
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from collections import defaultdict
from itertools import chain, product
import re

from mna import MNA



def test_B1():

    mna = MNA( 3)

    R1, R2, R3, R4 = .1, 0.5, 2, .1

    mna.add_r( 0, 1, R1)
    mna.add_r( 1, -1, R2)
    mna.add_r( 0, 2, R3)
    mna.add_r( 2, -1, R4)

    mna.add_c( 0, 1)
    mna.add_c( 1, 1)
    mna.add_c( 2, -1)

    mna.add_d( 5, 1) # i3

    mna.semantic()

    print(mna.a.todense())

    print(mna.x)

    print(mna.rel_sens_r(3), mna.rel_sens_r(4), mna.rel_sens_r(5), mna.rel_sens_r(6))

    assert np.isclose( mna.x[4], (R1 + 2*R3 + R4) / (R1 + R2 + R3 + R4)) # i2
    assert np.isclose( mna.x[5], (R1 + 2*R2 + R4) / (R1 + R2 + R3 + R4)) # i3

    f, g = R1 + 2*R2 + R4, R1 + R2 + R3 + R4
    # d(f/g)/dR1 = (gf' - fg') / g^2; f' = 1, g' = 1
    assert np.isclose( mna.sens_r(3), (g - f) / g**2)

    # d(f/g)/dR2 = (gf' - fg') / g^2; f' = 2, g' = 1
    assert np.isclose( mna.sens_r(4), (2*g - f) / g**2)

    # d(f/g)/dR3 = (gf' - fg') / g^2; f' = 0, g' = 1
    assert np.isclose( mna.sens_r(5), -f / g**2)

    # d(f/g)/dR4 = (gf' - fg') / g^2; f' = 1, g' = 1
    assert np.isclose( mna.sens_r(6), (g - f) / g**2)

