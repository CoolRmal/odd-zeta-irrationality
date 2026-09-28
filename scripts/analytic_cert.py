"""Design and interval-verification of the analytic certificate (BLUEPRINT §4-5).

Path L (lower half-plane): ray {Re u = Re bot, Im u <= Im bot}, sigma = [bot, top] with
bot = u* - v, top = u* + v, horizontal segment top -> x1 + i Im(top), vertical segment up to x1.
All checks are done on boxes with monotone bounds, as they will be in Lean.
"""
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, iv, pi, log, atan, findroot, arg, exp, fabs, sqrt
import params
from params import CASES, f1, f2, H

mp.dps = 60
iv.dps = 40


PAD = mpf('1e-45')
class I:
    """closed interval [lo, hi] with monotone elementary functions (padded, mp.dps = 60)."""
    def __init__(s, lo, hi=None):
        s.lo = mpf(lo); s.hi = mpf(lo if hi is None else hi)
    def __add__(s, o):
        o = o if isinstance(o, I) else I(o); return I(s.lo + o.lo - PAD, s.hi + o.hi + PAD)
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o): return s + (-(o if isinstance(o, I) else I(o)))
    def __rsub__(s, o): return I(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        ps = [s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi]; return I(min(ps) - PAD, max(ps) + PAD)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0
        return s * I(1/o.hi, 1/o.lo)
    def sq(s):
        if s.lo >= 0: return I(s.lo**2, s.hi**2)
        if s.hi <= 0: return I(s.hi**2, s.lo**2)
        return I(0, max(s.lo**2, s.hi**2))
def iatan(x): return I(atan(x.lo) - PAD, atan(x.hi) + PAD)
def ilog(x):
    assert x.lo > 0; return I(log(x.lo) - PAD, log(x.hi) + PAD)
IPI = I(pi - PAD, pi + PAD)

def frac_of(x, den=10**30):
    return Fr(int(mp.nint(x * den)), den)

def shifts(c):
    """(a, coeff) for Im f'(u) = sum coeff * arg(a + u); a = None stands for the term -r*arg(-u)."""
    r, e0, e = c['r'], c['eta0'], c['eta']
    L = [(e0, r)]
    for h in e:
        L += [(h, 1), (e0 - h, -1)]
    return L

def argI(x, y):
    """interval enclosure of arg(x + i y) for intervals x, y with x > 0 or y != 0 (iv)."""
    # use atan2 via iatan
    if x.lo > 0:
        return iatan(y / x)
    if y.hi < 0:
        return -IPI / 2 - iatan(x / y)
    if y.lo > 0:
        return IPI / 2 - iatan(x / y)
    raise ValueError('bad box')

def imf1_box(c, x, y):
    """enclosure of Im f'(u) over the box x × y (intervals), y < 0."""
    r = c['r']
    s = I(0)
    for a, co in shifts(c):
        s += co * argI(a + x, y)
    s -= r * argI(-x, -y)
    return s

def ref1_box(c, x, y):
    r = c['r']
    s = I(0)
    def lg(xx, yy):
        return ilog(xx * xx + yy * yy) / 2
    for a, co in shifts(c):
        s += co * lg(a + x, y)
    s -= r * lg(-x, -y)
    return s

def cover(lo, hi, test, minw=mpf('1e-6')):
    """adaptive subdivision of [lo, hi] until test(interval) holds; returns list of pieces."""
    out, stack = [], [(mpf(lo), mpf(hi))]
    while stack:
        a, b = stack.pop()
        if test(a, b):
            out.append((a, b))
        else:
            if b - a < minw:
                raise RuntimeError(f'cannot certify near {a}')
            m = (a + b) / 2
            stack += [(m, b), (a, m)]
    return sorted(out)

def design(name, x1, rho=mpf('1e-12')):
    c = CASES[name]; k = c['r'] - 2
    import path
    u = path.saddle(name)
    ph = (pi - arg(f2(c, u))) / 2
    e = exp(1j * ph)
    if e.imag < 0: e = -e
    ut = mpc(frac_of(u.real).numerator, 1) / frac_of(u.real).denominator  # placeholder
    ut = mpc(mpf(frac_of(u.real).numerator) / frac_of(u.real).denominator,
             mpf(frac_of(u.imag).numerator) / frac_of(u.imag).denominator)
    vr = Fr(round(float(e.real) * 1000), 1000); vi = Fr(round(float(e.imag) * 1000), 1000)
    v = mpc(mpf(vr.numerator) / vr.denominator, mpf(vi.numerator) / vi.denominator)
    top, bot = u + v, u - v
    a = -(v ** 2) * f2(c, u) / 2
    # third derivative bound on disc of radius |v| + small around u
    R = abs(v) + mpf('0.01')
    def dist(p):  # distance from u to branch point p minus R
        return abs(u - p) - R
    M3 = c['r'] * (1 / dist(-c['eta0']) ** 2 + 1 / dist(0) ** 2) + sum(1 / dist(-h) ** 2 + 1 / dist(-(c['eta0'] - h)) ** 2 for h in c['eta'])
    b = a.real - M3 * abs(v) ** 3 / 6
    Hd = H(c, k, u)
    print(f'{name}: u*={mp.nstr(u, 15)} v={vr}+{vi}i Re a={mp.nstr(a.real, 6)} M3={mp.nstr(M3, 6)} b={mp.nstr(b, 6)} Hd={mp.nstr(Hd, 12)} alpha mod pi={mp.nstr((params.f(c,u) + 1j*k*pi*u).imag % pi, 8)}')
    eps = mpf('1e-9')
    xb = I(bot.real - eps, bot.real + eps); yb = bot.imag
    # ray: need Im f' + k pi <= -cdec on y in (-inf, yb]
    cdec = mpf('0.2')
    def ray_ok(lo, hi):
        val = imf1_box(c, xb, I(lo, hi)) + k * IPI
        return val.hi <= -cdec
    Ybig = mpf(10) ** 4
    ray = cover(-Ybig, yb, lambda lo, hi: ray_ok(lo, hi))
    # horizontal: Re f' > 0 on x in [x1, Re top], y = Im top
    yt = I(top.imag - eps, top.imag + eps)
    assert x1 < top.real
    hor = cover(x1, top.real + eps, lambda lo, hi: ref1_box(c, I(lo, hi), yt).lo > 0)
    # vertical: Im f' + k pi > 0 on x = x1, y in [Im top, 0)
    ver = cover(top.imag - eps, mpf(0), lambda lo, hi: (imf1_box(c, I(x1), I(lo, hi)) + k * IPI).lo > 0)
    print(f'   boxes: ray {len(ray)}, horizontal {len(hor)}, vertical {len(ver)}')
    return dict(u=u, v=v, ray=ray, hor=hor, ver=ver)

if __name__ == '__main__':
    design('A', mpf(-2))
    design('A', mpf(-3)/2)
    design('B', mpf(-1) / 2)
