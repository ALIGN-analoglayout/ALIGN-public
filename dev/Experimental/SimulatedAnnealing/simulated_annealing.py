import math
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
matplotlib.use('Agg')


# Default hyperparameter values
plt.figure()
delta_lst = [0.1]
for delta in delta_lst:
    t_init = 1e6
    t_min = 1/t_init
    alpha = 0.995
    n_iter = int(math.log(t_min/t_init)/math.log(alpha))
    p = []
    t = t_init
    for i in range(n_iter):
        p.append(math.exp(-delta/t))
        t *= alpha
    assert np.allclose(t_min, t)
    plt.plot(range(n_iter), p)
plt.title(f'Acceptance Probability for {int(delta*100)}% Inferior Solution')
plt.show()
plt.legend(delta_lst)
plt.savefig("acceptance_probability_default.png")


# Vary t_init for n_iter=15k
plt.figure()
t_init_lst = [1e1, 1e2, 1e3, 1e4, 1e5, 1e6]
alpha_lst = []
for t_init in t_init_lst:
    delta = 0.1
    n_iter = int(15000)
    t_min = 1/t_init
    alpha = math.exp(math.log(t_min/t_init)/n_iter)
    alpha_lst.append(alpha)
    p = []
    t = t_init
    for i in range(n_iter):
        p.append(math.exp(-delta/t))
        t *= alpha
    assert np.allclose(t_min, t)
    plt.plot(range(n_iter), p)
plt.title(f'Acceptance Probability for {int(delta*100)}% Inferior Solution')
lgd = [f't_init={int(a)}, alpha={b:0.4f}' for a, b in zip(t_init_lst, alpha_lst)]
plt.legend(lgd)
plt.grid()
plt.ylabel('Probability')
plt.xlabel('Iterations')
plt.savefig("acceptance_probability.png")


def median_cost_geometric(n_iter, t_init, alpha):
    c = []
    t = t_init
    for i in range(n_iter):
        """
        r <= exp(-c/T)
        0.5 = exp(-c/T)
        c_median = T*ln(2)
        c_median_pct = 100*T*ln(2)
        """
        c.append(100*t*math.log(2))
        t *= alpha
    return(c)


def median_cost_harmonic(n_iter, t_init):
    c = []
    t = t_init
    t_lst = []
    for i in range(n_iter):
        """
        r <= exp(-c/T)
        0.5 = exp(-c/T)
        c_median = T*ln(2)
        c_median_pct = 100*T*ln(2)
        """
        c.append(100*t*math.log(2))
        t = t_init
        t = t_init*(n_iter/(i+1)-1)/(n_iter-1)
    return(c, t_lst)


def median_cost_linear(n_iter, t_init):
    c = []
    t = t_init
    t_lst = []
    dt = t_init/n_iter
    for i in range(n_iter):
        """
        r <= exp(-c/T)
        0.5 = exp(-c/T)
        c_median = T*ln(2)
        c_median_pct = 100*T*ln(2)
        """
        c.append(100*t*math.log(2))
        t = t_init - dt*i
    return(c, t_lst)


# Median cost for geometric annealing
plt.figure()
n_iter = int(10000)
t_init_lst = [1e2, 1e4, 1e6]
alpha_lst = []
for t_init in t_init_lst:
    t_min = 1/t_init
    alpha = math.exp(math.log(t_min/t_init)/n_iter)
    alpha_lst.append(alpha)
    c = median_cost_geometric(n_iter, t_init, alpha)
    plt.semilogy(range(n_iter), c)
plt.title('Geometric Annealing from t_init to 1/t_init')
lgd = [f't_init={a:.2f}, alpha={b:0.4f}' for a, b in zip(t_init_lst, alpha_lst)]
plt.legend(lgd)
plt.show()
plt.grid()
plt.ylabel('Median Value of Accepted Cost')
plt.xlabel('Iterations')
plt.savefig("median_cost_geometric.png")


# Median cost for linear annealing
plt.figure()
n_iter = int(10000)
t_init_lst = [1, 2, 4]
alpha_lst = []
for t_init in t_init_lst:
    (c, t) = median_cost_harmonic(n_iter, t_init)
    plt.semilogy(range(n_iter), c)
plt.title('Linear Annealing from t_init to 0')
lgd = [f't_init={a:.2f}' for a in t_init_lst]
plt.legend(lgd)
plt.show()
plt.grid()
plt.ylabel('Median Value of Accepted Cost')
plt.xlabel('Iterations')
plt.savefig("median_cost_harmonic.png")


# Median cost for linear annealing
plt.figure()
n_iter = int(10000)
t_init_lst = [1, 2, 4]
alpha_lst = []
for t_init in t_init_lst:
    (c, t) = median_cost_linear(n_iter, t_init)
    plt.plot(range(n_iter), c)
plt.title('Linear Annealing from t_init to 0')
lgd = [f't_init={a:.2f}' for a in t_init_lst]
plt.legend(lgd)
plt.show()
plt.grid()
plt.ylabel('Median Value of Accepted Cost')
plt.xlabel('Iterations')
plt.savefig("median_cost_linear.png")


# Median cost for geometric annealing
plt.figure()
n_iter = int(10000)
t_init_lst = [0.75]
alpha_lst = []
for t_init in t_init_lst:
    t_min = t_init/n_iter
    alpha = 0.99925
    alpha_lst.append(alpha)
    c = median_cost_geometric(n_iter, t_init, alpha)
    plt.plot(range(n_iter), c)
plt.title('Geometric Annealing')
lgd = [f't_init={a:.2f}, alpha={b:0.5f}' for a, b in zip(t_init_lst, alpha_lst)]
plt.legend(lgd)
plt.show()
plt.grid()
plt.ylabel('Median Value of Accepted Cost')
plt.xlabel('Iterations')
plt.savefig("median_cost_geometric_v2.png")

#
t = 0.75
plt.figure()
pct = np.linspace(1, 10, 100)

delta = pct
p = np.exp(-delta/t)
plt.plot(pct, p)

delta = np.log(pct)
p = np.exp(-delta/t)
plt.plot(pct, p)

plt.grid()
plt.title(f'Acceptance Probability at T_INIT={t}')
plt.ylabel('Acceptance Probability')
plt.xlabel('trial_cost/current_cost')
plt.xlim([1, 10])
plt.ylim([0, 1])
plt.legend(['linear: r < exp( -(c1/c2)/T )', 'log: r < exp( -log(c1/c2)/T ) '])
plt.savefig("acceptance_vs_ratio.png")
