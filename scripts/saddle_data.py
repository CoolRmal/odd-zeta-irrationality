"""Rational data for the saddle-point certificates (OddZeta/Cert), checked with exactly the
corner formulas of OddZeta/Cert/ToolsAux3,4 (`im_f'_le_box`, `le_im_f'_box`, `re_f'_pos_box`)."""
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, atan2, atan, log, pi, findroot, fabs
import params, path
from params import CASES, f, f1, f2

mp.dps = 50
PAD = mpf(10) ** -30

def M(x):
    return mpf(x.numerator) / x.denominator if isinstance(x, Fr) else mpf(x)

def arg(a, b):  # principal arg of a + bi, a, b Fractions/mpf
    return atan2(M(b), M(a))

def shifts(c):
    return c['eta']

def im_upper(c, x1, x2, y1, y2):
    r, e0 = c['r'], c['eta0']
    s = r * (arg(e0 + x2, y2) - min(arg(-x1, -y1), arg(-x1, -y2)))
    for h in c['eta']:
        s += arg(h + x2, y2) - arg(e0 - h + x1, y1)
    return s + PAD

def im_lower(c, x1, x2, y1, y2):
    r, e0 = c['r'], c['eta0']
    s = r * (arg(e0 + x1, y1) - max(arg(-x2, -y1), arg(-x2, -y2)))
    for h in c['eta']:
        s += arg(h + x1, y1) - arg(e0 - h + x2, y2)
    return s - PAD

def re_box_ok(c, x1, x2, y1, y2):
    r, e0 = c['r'], c['eta0']
    lhs = (max(x1 * x1, x2 * x2) + y1 * y1) ** r
    rhs = ((e0 + x1) ** 2 + y2 * y2) ** r
    for h in c['eta']:
        lhs *= (e0 - h + x2) ** 2 + y1 * y1
        rhs *= (h + x1) ** 2 + y2 * y2
    return lhs < rhs

def cover(lo, hi, ok, minw=Fr(1, 10 ** 6)):
    out, stack = [], [(lo, hi)]
    while stack:
        a, b = stack.pop()
        if ok(a, b):
            out.append((a, b))
        else:
            assert b - a > minw, f'cannot certify near {float(a)}'
            m = (a + b) / 2
            m = Fr(round(m * 1024), 1024) if a < Fr(round(m * 1024), 1024) < b else m
            stack += [(m, b), (a, m)]
    return sorted(out)

def rat(x, den=10 ** 20):
    return Fr(int(mp.nint(mpf(x) * den)), den)

def design(name, v, x1, rho=Fr(1, 10 ** 10), Y=10 ** 4, c_ray=Fr(1, 5)):
    c = CASES[name]; k = c['r'] - 2
    u = path.saddle(name)
    ut = (rat(u.real), rat(u.imag))
    vr, vi = v
    kpi = k * pi
    # ray: x in [Re(ut - v) - rho, + rho], y in [-Y, Im(ut - v) + rho]
    bx1, bx2 = ut[0] - vr - rho, ut[0] - vr + rho
    ray = cover(Fr(-Y), ut[1] - vi + rho, lambda a, b: im_upper(c, bx1, bx2, a, b) + kpi <= -M(c_ray))
    # tail condition: -2pi + r (eta0 + 2|x|)/Y <= -c
    tail = -2 * pi + c['r'] * M(c['eta0'] + 2 * max(abs(bx1), abs(bx2))) / Y
    assert tail <= -M(c_ray)
    # horizontal: x in [x1, Re(ut+v)+rho], y in [Im(ut+v) - rho, Im(ut+v)+rho]
    ty1, ty2 = ut[1] + vi - rho, ut[1] + vi + rho
    hor = cover(x1, ut[0] + vr + rho, lambda a, b: re_box_ok(c, a, b, ty1, ty2))
    # vertical: x = x1, y in [Im(ut+v) - rho, 0]
    ver = cover(ty1, Fr(0), lambda a, b: im_lower(c, x1, x1, a, b) + kpi > 0)
    print(f'{name}: ut = {float(ut[0]):.12f} {float(ut[1]):.12f}; boxes ray {len(ray)} hor {len(hor)} ver {len(ver)}; tail {float(tail):.3f}')
    return dict(ut=ut, v=v, x1=x1, rho=rho, Y=Y, ray=ray, hor=hor, ver=ver)

if __name__ == '__main__':
    import json
    out = {}
    for name, v, x1 in [('A', (Fr(-269, 500), Fr(843, 1000)), Fr(-3, 2)),
                        ('B', (Fr(-353, 500), Fr(177, 250)), Fr(-1, 2))]:
        d = design(name, v, x1)
        out[name] = {k: (str(v) if not isinstance(v, (list, tuple)) else
                         [[str(a), str(b)] if isinstance(a, Fr) or isinstance(b, Fr) else str(a) for a, b in v] if k in ('ray', 'hor', 'ver') else [str(x) for x in v])
                     for k, v in d.items()}
    json.dump(out, open('saddle_data.json', 'w'), indent=1)
