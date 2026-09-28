"""The function φ of Section 3.1 (exact rational arithmetic) and the constant C2 of Lemma 3.3."""
from fractions import Fraction as Fr
from math import floor
from params import CASES

def mhat(c):
    r, e0, e = c['r'], c['eta0'], c['eta']
    m0 = max(e[r - 1], e0 - 2 * e[r])
    return m0, [max(m0, e0 - e[0] - e[r + j - 1]) for j in range(1, c['q'] - r + 1)]

def phi0(c, x, y):
    r, e0, e = c['r'], c['eta0'], c['eta']
    s = 0
    for j, h in enumerate(e):
        if j < r:
            s += floor(y) + floor(e0 * x - y) - floor(y - h * x) - floor((e0 - h) * x - y) - 2 * floor(h * x)
        else:
            s += floor((e0 - 2 * h) * x) - floor(y - h * x) - floor((e0 - h) * x - y)
    return s

def phi(c, x):
    """min over y in [0,1) of phi0(x, y); exact for rational x."""
    e0, e = c['eta0'], c['eta']
    A = {0, e0} | set(e) | {e0 - h for h in e}
    pts = sorted({(a * x) % 1 for a in A} | {Fr(0)})
    cand = list(pts) + [(pts[i] + pts[i + 1]) / 2 for i in range(len(pts) - 1)] + [(pts[-1] + 1) / 2]
    return min(phi0(c, x, y) for y in cand)

def breakpoints(c):
    r, e0, e = c['r'], c['eta0'], c['eta']
    _, m = mhat(c)
    A = sorted({0, e0} | set(e) | {e0 - h for h in e})
    dens = {abs(a - b) for a in A for b in A if a != b} | set(e[:r]) | {e0 - 2 * h for h in e[r:]} | {m[-1]}
    X = {Fr(a, b) for b in dens for a in range(0, b + 1)}
    return sorted(X)
