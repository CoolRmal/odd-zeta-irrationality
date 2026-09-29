"""Test the monotone path design of OddZeta/Cert (ray below bot, sigma, horizontal, vertical)
for the uniform family eta^(r)."""
import sys
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, pi, arg, exp, sqrt, fabs
import params
from family import fam, saddle_family
import saddle_data as SD
mp.dps = 40

def try_r(r, u, x1s=(-6, -4, -3, -2, -1, Fr(-1, 2), Fr(-1, 4))):
    c = fam(r); k = r - 2
    f2 = params.f2(c, u)
    ph = (pi - arg(f2)) / 2
    e = exp(1j * ph)
    if e.imag < 0: e = -e
    # third derivative bound on a disc: crude via finite sample; choose s0
    best = None
    for s0 in [mpf(x) / 10 for x in range(12, 2, -1)]:
        v = s0 * e
        top, bot = u + v, u - v
        if top.imag >= -0.02 or bot.imag >= -0.02:
            continue
        # sigma decay numerically
        ok = all((params.f(c, u + s * v) + 1j*k*pi*(u+s*v) - params.f(c, u) - 1j*k*pi*u).real <= -0.2 * s * s * abs(f2) * s0**2 for s in [mpf(i)/10 for i in range(-10, 11) if i])
        if not ok:
            continue
        best = (s0, v, top, bot)
        break
    if best is None:
        return 'no s0'
    s0, v, top, bot = best
    vr = Fr(round(float(v.real) * 1000), 1000); vi = Fr(round(float(v.imag) * 1000), 1000)
    last = f'no x1 < top.re={float(top.real):.3f}'
    for x1 in x1s:
        if Fr(x1) >= Fr(round(float(top.real)*1000),1000):
            continue
        try:
            params.CASES['fam'] = c
            import saddle_data
            saddle_data.CASES['fam'] = c
            path_mod = __import__('path')
            path_mod.SADDLE0['fam'] = u
            d = SD.design('fam', (vr, vi), Fr(x1))
            return f's0={float(s0)} x1={x1} boxes ray {len(d["ray"])} hor {len(d["hor"])} ver {len(d["ver"])}'
        except (AssertionError, Exception) as ex:
            last = str(ex)[:60]
    return 'fail: ' + last

if __name__ == '__main__':
    rs = list(range(3, 52, 2))
    S = saddle_family(rs)
    for r in rs:
        print(r, complex(S[r]), try_r(r, S[r]), flush=True)
