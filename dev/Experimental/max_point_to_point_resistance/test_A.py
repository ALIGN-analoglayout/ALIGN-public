import pytest

import numpy as np
import scipy.linalg as la

from scipy import sparse
import scipy.sparse.linalg as sla

from collections import defaultdict
import itertools


def par(a, b):
    return a*b/(a+b)

def wye2del(a, b, c):
    s = a*b + a*c + b*c
    # bc, ac, ab
    return s/a, s/b, s/c

def grid5():

    bc, ac, ab = wye2del(0.5, 0.5, 1)
    bc = par(bc, 0.5)

    tmp = ac

    a = ab
    b = bc
    c = 0.75

    bc, ac, ab = wye2del(a, b, c)

    return 2*par(par(tmp, ab) + par(0.25, bc), ac)

def grid6():

    x_uv, x_ov, x_ou = wye2del(0.5, 0.5, 0.5)
    
    q_vt, q_uv, q_ut = wye2del(0.5, 0.25, 0.5)
    
    ou = x_ou
    ov = par(1, x_ov)
    uv = par(x_uv, q_uv)
    ut = par(0.75, q_ut)
    vt = par(1, q_vt)

    u_ot, u_ov, u_tv = wye2del(uv, ut, ou)

    return 2*(par(par(ov, u_ov) + par(vt, u_tv), u_ot) + 0.5)

def stamp(lst, ref, ports):
    # lst is a list of triples two nodes and a conductance

    all_nodes = set()
    for (a, b, g) in lst:
        all_nodes.add(a)
        all_nodes.add(b)

    mapping = {}

    for a in all_nodes:
        if a == ref:
            pass
        elif a in ports:
            pass
        else:
            if a not in mapping:
                mapping[a] = len(mapping)

    split_point = len(mapping)

    for a in all_nodes:
        if a == ref:
            pass
        elif a in ports:
            if a not in mapping:
                mapping[a] = len(mapping)

    nports = len(mapping) - split_point

    mapping[ref] = None


    new_lst = []
    for (a, b, g) in lst:
        new_lst.append((mapping[a], mapping[b], g))


    A = defaultdict(float)
    B = defaultdict(float)
    C = defaultdict(float)
    D = defaultdict(float)

    def update(i, j, incr):
        if i < split_point and j < split_point:
            A[(i,j)] += incr
        elif i < split_point and j >= split_point:
            B[(i,j-split_point)] += incr
        elif i >= split_point and j < split_point:
            C[(i-split_point,j)] += incr
        elif i >= split_point and j >= split_point:
            D[(i-split_point,j-split_point)] += incr

    for (a, b, g) in new_lst:
        if a is not None:
            update(a, a, g)

        if a is not None and b is not None:            
            update(a, b, -g)
            update(b, a, -g)

        if b is not None:
            update(b, b, g)

    def build_sparse(M, rows, cols):
        i = [i for ((i, j), g) in M.items()]
        j = [j for ((i, j), g) in M.items()]
        g = [g for ((i, j), g) in M.items()]
        return sparse.coo_array((g, (i,j)), shape=(rows,cols)).tocsc()

    return \
        build_sparse(A, split_point, split_point), \
        build_sparse(B, split_point, nports), \
        build_sparse(C, nports, split_point), \
        build_sparse(D, nports, nports)

def inverse_schur_complement(A, B, C, D):
    # A x0 + B x1 = 0
    # C x0 + D x1 = b1
    # x0 = -A^-1 B x1
    # (D - C A^-1 B) x1 = b1

    S = D - C @ sla.spsolve(A, B)
    print(f'S: {S} {S.shape}')
    return la.inv(S.todense())

def max_pin_to_pin_resistance(Sinv):
    # (u_i-u_j)^T Sinv (u_i-u_j)
    return max(Sinv[i,i] - Sinv[i,j] - Sinv[j,i] + Sinv[j,j] for (i,j) in itertools.combinations(range(Sinv.shape[0]), 2))

def build_and_solve(lst, ref, ports):
    A, B, C, D = stamp(lst, ref, ports)
    # print(f'A: {A} {A.shape}')
    # print(f'B: {B} {B.shape}')
    # print(f'C: {C} {C.shape}')
    # print(f'D: {D} {D.shape}')

    Sinv = inverse_schur_complement(A, B, C, D)
    print(f'Sinv: {Sinv}')
    computed_max_pin_to_pin_resistance = max_pin_to_pin_resistance(Sinv)
    print(f'computed_max_pin_to_pin_resistance: {computed_max_pin_to_pin_resistance}')
    return computed_max_pin_to_pin_resistance

def test_stamp():
    # 0   1   2   3   4
    # T---x---G---x---T

    res = build_and_solve([(0,1,1), (1,2,1), (2,3,1), (3,4,1)], 2, set([0,4]))
    assert abs(res-4) < 0.001

def test_stamp1():
    # 0   1   2   3   4   5
    # G---T---x---T---x---T
    res = build_and_solve([(0,1,1), (1,2,1), (2,3,1), (3,4,1), (4,5,1)], 0, set([1,3,5]))
    assert abs(res-4) < 0.001

@pytest.mark.parametrize("n", [2,3,4,5,6])
def test_stamp_square_corners(n):
    def idx(i,j):
        return n*i + j

    lst = []
    for i in range(n):
        for j in range(1, n):
            lst.append((idx(i,j-1),idx(i,j),1))
    for j in range(n):
        for i in range(1, n):
            lst.append((idx(i-1,j),idx(i,j),1))

    print(f'lst: {lst}')
    res = build_and_solve(lst, n*n//2, set([idx(0,0),idx(n-1,n-1)]))

    gold = { 2: 1, 3: 3/2, 4: 13/7, 5: grid5(), 6: grid6() }
    print(f'n: {n} res: {res} gold: {gold[n]} diff: {res-gold[n]}')
    assert abs(res-gold[n]) < 0.001

def test_stamp2():
    #    0   1   2   3   4
    #  0 T---x---x---x---T
    #    |   |   |   |   |
    #  5 x---x---x---x---x
    #    |   |   |   |   |
    # 10 x---x---G---x---x
    #    |   |   |   |   |
    # 15 x---x---x---x---x
    #    |   |   |   |   |
    # 20 T---x---x---x---T
    #

    res = build_and_solve([
        (0,1,1), (1,2,1), (2,3,1), (3,4,1),
        (5,6,1), (6,7,1), (7,8,1), (8,9,1),
        (10,11,1), (11,12,1), (12,13,1), (13,14,1),
        (15,16,1), (16,17,1), (17,18,1), (18,19,1),
        (20,21,1), (21,22,1), (22,23,1), (23,24,1),
        (0,5,1), (1,6,1), (2,7,1), (3,8,1), (4,9,1),
        (5,10,1), (6,11,1), (7,12,1), (8,13,1), (9,14,1),
        (10,15,1), (11,16,1), (12,17,1), (13,18,1), (14,19,1),
        (15,20,1), (16,21,1), (17,22,1), (18,23,1), (19,24,1)
    ], 12, set([0,4,20,24]))

    assert abs(res-grid5()) < 0.001

def test_stamp3():
    #    0   1
    #  0 T---x
    #    |   |
    #  2 x---T

    res = build_and_solve([
        (0,1,1),
        (2,3,1),
        (0,2,1),
        (1,3,1)
    ], 1, set([0,3]))

    assert abs(res-1) < 0.001

def test_stamp4():
    #    0   1
    #  0 T---x
    #    |   |
    #  2 x   x
    #    |   |
    #  4 x---T

    res = build_and_solve([
        (0,1,1),
        (4,5,1),
        (0,2,1),
        (1,3,1),
        (2,4,1),
        (3,5,1)
    ], 1, set([0,5]))

    assert abs(res-3/2) < 0.001


def test_stamp5():
    #    0   1
    #  0 T---x
    #    |   |
    #  2 x---x
    #    |   |
    #  4 x---T

    res = build_and_solve([
        (0,1,1),
        (2,3,1),
        (4,5,1),
        (0,2,1),
        (1,3,1),
        (2,4,1),
        (3,5,1)
    ], 1, set([0,5]))

    assert abs(res-7/5) < 0.001


def power_method(B, x):

    n = B.shape[0]

    def normalize(x):
        #fac = np.abs(x).max()
        fac = np.sqrt(x.dot(x))
        x_n = x / fac
        return fac, x_n

    for i in range(8):
        x = B.dot(x)
        lambda_1, x = normalize(x)
        print(lambda_1, x)

    return lambda_1, x


def max_point_to_point_resistance(T):
    n = T.shape[0]

    factors, pivot = la.lu_factor(T)
    lu, d, perm = la.ldl(T)

    print('factors, pivot:')
    print(factors, pivot)
    print('lu, d, perm:')
    print(lu, d, perm)

    print('c, lower:')
    c, lower = la.cho_factor(T)
    print(c, lower)

    new_factors = factors[2:, 2:]
    new_pivot = np.array([0, 1, 2], dtype=np.int32)
    print( factors[2:, 2:].shape)
    b = np.zeros(3)
    XX = []
    
    for i in range(3):
        b[i] = 1
        XX.append(la.lu_solve((new_factors, new_pivot), b))
        b[i] = 0

    print('XX', XX)



    X = []
    X2 = []
    b = np.zeros(n)
    for i in range(n):
        b[i] = 1
        X.append(la.lu_solve( (factors, pivot), b))
        X2.append(la.cho_solve( (c, lower), b))
        b[i] = 0

    print(b, X)
    print(b, X2)

    B = la.inv(T)
    print('B')
    print(B)

    return

    result = la.eig(B)
    print('Eigensystem:')
    print(result)

    x = np.array([1,1,1,1,1],dtype=np.float64)
    power_method(B, x)

    for i, j in itertools.combinations(range(n+1), 2):
        x = np.zeros(shape=(n,))
        if i > 0:
            x[i-1] -= 1
        if j > 0:
            x[j-1] += 1
        print(i, j, x, x.dot(B.dot(x)))


def test_A():

    T = np.array([[1, -1, 0, 0, 0], [-1, 2, -1, 0, 0], [0, -1, 2, 0, 0], [0, 0, 0, 2, -1], [0, 0, 0, -1, 1]])

    max_point_to_point_resistance(T)

def test_B():

    T = np.array([[1, -1, 0, 0, 0], [-1, 2, -1, 0, 0], [0, -1, 2, -1, 0], [0, 0, -1, 2, -1], [0, 0, 0, -1, 2]])

    max_point_to_point_resistance(T)

def test_C():
  
    # G   2   0   3   1   4
    # x---T---x---T---x---T


    #               0  1  2  3  4
    T = np.array([[ 2, 0,-1,-1, 0],
                  [ 0, 2, 0,-1,-1],
                  [-1, 0, 2, 0, 0],
                  [-1,-1, 0, 2, 0],
                  [ 0,-1, 0, 0, 1]])

    max_point_to_point_resistance(T)

