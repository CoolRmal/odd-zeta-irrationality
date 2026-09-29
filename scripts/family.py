"""The uniform family eta^(r) = (150; 45^r; 48^r,50^r,53^r,56^r,60^r, 74) of Section 8."""
from mpmath import mp, mpf, mpc, log, pi, findroot, arg, exp
import params

def fam(r):
    return dict(r=r, eta0=150, eta=[45] * r + [48] * r + [50] * r + [53] * r + [56] * r + [60] * r + [74], q=6 * r + 1)

BASE = dict(r=1, eta0=150, eta=[45, 48, 50, 53, 56, 60], q=6)

# structural form (Section 8.1): g, e and F = r g + e - 2 pi i u on the lower half plane
Z0, PS, PE = 45, [48, 50, 53, 56, 60], 74
CB = [(0, -1), (150, 1), (Z0, 1), (150 - Z0, -1)] + [(p, 1) for p in PS] + [(150 - p, -1) for p in PS]

def xl(w):
    return w * log(w)

def g(u):
    s = -u * log(u) + xl(150 + u) + xl(Z0 + u) - xl(150 - Z0 + u) - 2 * Z0 * log(Z0)
    for p in PS:
        s += xl(p + u) - xl(150 - p + u) + (150 - 2 * p) * log(150 - 2 * p)
    return s

def e(u):
    return xl(PE + u) - xl(150 - PE + u) + (150 - 2 * PE) * log(150 - 2 * PE)

def g1(u):
    return sum(c * log(b + u) for b, c in CB)

def e1(u):
    return log(PE + u) - log(150 - PE + u)

def g2(u):
    return sum(c / (b + u) for b, c in CB)

def e2(u):
    return 1 / (PE + u) - 1 / (150 - PE + u)

def Fs(r, u):
    return r * g(u) + e(u) - 2j * pi * u

def F1s(r, u):
    return r * g1(u) + e1(u) - 2j * pi

def saddle_family(rs, start=None):
    """continuation from large r downwards; returns {r: u*}"""
    out = {}
    a = findroot(lambda x: g1(x), mpf('4.19'))
    D = -g2(a)
    for r in sorted(rs, reverse=True):
        guess = start if start is not None else a - 2j * pi / (r * D)
        u = findroot(lambda u: F1s(r, u), guess)
        out[r] = u
        start = u
    return out
