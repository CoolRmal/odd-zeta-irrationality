"""Paths of Section 5.1 and the values of H_{r-2} along them."""
from mpmath import mp, mpf, mpc, exp, pi, arg, findroot, fabs
from params import CASES, f, f1, f2, H

SADDLE0 = {'A': mpc(-0.590758658259, -9.722688491285), 'B': mpc(2.414446160185, -6.698929997253),
           'C': mpc(-3.204559550730, -3.103130294133)}
X0 = {'A': -2, 'B': -2, 'C': mpf('-3.46088652')}

def saddle(name):
    c = CASES[name]; k = c['r'] - 2
    u = findroot(lambda u: f1(c, u) + 1j * k * pi, SADDLE0[name])
    return u

def paper_path(name, s0=1, s1=1):
    c = CASES[name]; k = c['r'] - 2
    u = saddle(name)
    ph = (pi - arg(f2(c, u))) / 2
    e = exp(1j * ph)
    if (e).imag < 0:
        e = -e
    top, bot, ext = u + s0 * e, u - s0 * e, u - (s0 + s1) * e
    return dict(u=u, e=e, top=top, bot=bot, ext=ext, x0=mpf(X0[name]))
