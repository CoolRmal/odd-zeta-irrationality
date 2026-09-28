"""Direction vectors of the note (Section 1) and the auxiliary functions of Section 4."""
from mpmath import mp, mpf, mpc, log, pi, findroot, sqrt, arg, fabs

CASES = {
    'A': dict(r=5, eta0=196, eta=[58, 58, 58, 59, 60, 62, 62, 63, 64, 64, 65, 66, 66, 68, 69, 70,
                                   72, 73, 75, 76, 77, 79, 80]),
    'B': dict(r=7, eta0=151, eta=[46, 46, 46, 46, 46, 46, 46, 47, 47, 48, 49, 49, 49, 50, 51, 51,
                                   51, 52, 53, 53, 53, 54, 55, 55, 55, 56, 57, 57, 57, 58, 59, 59,
                                   59, 60, 61]),
    'C': dict(r=3, eta0=90, eta=[27, 27, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]),
}
for c in CASES.values():
    c['q'] = len(c['eta'])

def kappa0(c):
    r, e0, e = c['r'], c['eta0'], c['eta']
    return sum((e0 - 2 * x) * log(e0 - 2 * x) for x in e[r:]) - 2 * sum(x * log(x) for x in e[:r])

def xlogx(w):
    return w * log(w)

def f(c, u):
    r, e0, e = c['r'], c['eta0'], c['eta']
    s = r * (xlogx(-u) + xlogx(e0 + u))
    for x in e:
        s += xlogx(x + u) - xlogx(e0 - x + u)
    return s + kappa0(c)

def f1(c, u):
    r, e0, e = c['r'], c['eta0'], c['eta']
    s = r * (log(e0 + u) - log(-u))
    for x in e:
        s += log(x + u) - log(e0 - x + u)
    return s

def f2(c, u):
    r, e0, e = c['r'], c['eta0'], c['eta']
    s = r * (1 / (e0 + u) - 1 / u)
    for x in e:
        s += 1 / (x + u) - 1 / (e0 - x + u)
    return s

def H(c, k, u):
    return (f(c, u)).real - k * pi * u.imag
