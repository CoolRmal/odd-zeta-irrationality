"""Generate OddZeta/Cert/SaddleData.lean (the `SData` records of the saddle-point certificates)
from saddle_data.json, and sanity-check the rational side conditions of OddZeta/Cert/Machinery.lean
(`chkBasic`, the bounds `m`, `M3`, `bQ > 0`) with exact arithmetic."""
import json, os, sys
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, pi
sys.path.insert(0, os.path.dirname(__file__))
from params import CASES, f, f2

mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'OddZeta', 'Cert', 'SaddleData.lean')


def lowabs(a, b):
    return max(max(a, -b), Fr(0))


def nsqlow(xl, xh, yl, yh):
    return lowabs(xl, xh) ** 2 + lowabs(yl, yh) ** 2


def f3box(c, xl, xh, yl, yh):
    r, e0, eta = c['r'], c['eta0'], c['eta']
    s = r * (1 / nsqlow(e0 + xl, e0 + xh, yl, yh) + 1 / nsqlow(xl, xh, yl, yh))
    for h in eta:
        s += 1 / nsqlow(h + xl, h + xh, yl, yh) + 1 / nsqlow(e0 - h + xl, e0 - h + xh, yl, yh)
    return s


def f2exact(c, x, y):
    r, e0, eta = c['r'], c['eta0'], c['eta']

    def inv(a, b):
        n = a * a + b * b
        return (a / n, -b / n)
    re = im = Fr(0)
    a1, a2 = inv(e0 + x, y), inv(x, y)
    re += r * (a1[0] - a2[0]); im += r * (a1[1] - a2[1])
    for h in eta:
        b1, b2 = inv(h + x, y), inv(e0 - h + x, y)
        re += b1[0] - b2[0]; im += b1[1] - b2[1]
    return re, im


def lean_rat(q):
    q = Fr(q)
    if q.denominator == 1:
        return f'({q.numerator} : ℚ)'
    return f'mkRat ({q.numerator}) {q.denominator}'


def lean_list(l):
    return '[' + ', '.join(lean_rat(q) for q in l) + ']'


def make(name, D, V, m, M3, c_ray, H, m0, prec=60):
    c = CASES[name]
    r, e0 = c['r'], c['eta0']
    etaOne = min(c['eta'][:r])
    ur, ui = map(Fr, D['ut'])
    vr, vi = map(Fr, D['v'])
    x1, rho, Y = Fr(D['x1']), Fr(D['rho']), Fr(D['Y'])
    R = V + rho
    # chkBasic
    conds = [0 < rho, 0 <= V, vr ** 2 + vi ** 2 <= V ** 2, ui + R < 0, 0 < c_ray, 0 < Y,
             x1 <= Fr(-1, 2), Fr(1, 2) - etaOne <= x1, Fr(1, 2) <= e0 + 2 * x1,
             x1 < ur + vr - rho, x1 <= ur - vr - rho, ui + vi + rho <= Fr(-1, 2),
             ui - vi + rho <= Fr(-1, 2), ur - vr + rho + (ui - vi + rho) <= 0,
             ur + vr + rho + (ui + vi + rho) <= 0, x1 + (ui + vi + rho) <= 0,
             -2 * Fr(314159, 100000) + r * (e0 + 2 * max(-(ur - vr - rho), ur - vr + rho)) / Y
             <= -c_ray]
    assert all(conds), [i for i, b in enumerate(conds) if not b]
    # covers
    ray = [(Fr(a), Fr(b)) for a, b in D['ray']]
    hor = [(Fr(a), Fr(b)) for a, b in D['hor']]
    ver = [(Fr(a), Fr(b)) for a, b in D['ver']]
    for cov in (ray, hor, ver):
        assert all(cov[i][1] == cov[i + 1][0] for i in range(len(cov) - 1))
    assert ray[0][0] == -Y and ray[-1][1] >= ui - vi + rho
    assert hor[0][0] == x1 and hor[-1][1] >= ur + vr + rho
    assert ver[-1][1] == 0 and ver[0][0] <= ui + vi - rho
    # chkSaddle / chkSigma
    F = f2exact(c, ur, ui)
    assert m > 0 and m ** 2 <= F[0] ** 2 + F[1] ** 2
    M3b = f3box(c, ur - R, ur + R, ui - R, ui + R)
    assert M3b <= M3, float(M3b)
    assert M3 * rho <= m / 2
    aQ = -(F[0] * (vr ** 2 - vi ** 2) - F[1] * (2 * vr * vi)) / 2
    bQ = aQ - M3 * rho * (vr ** 2 + vi ** 2) / 2 - M3 * V ** 3 / 6
    assert bQ > 0
    # H and alpha (floating point)
    u = mpc(mpf(ur.numerator) / ur.denominator, mpf(ui.numerator) / ui.denominator)
    Fd = f(c, u) + 1j * (r - 2) * pi * u
    assert Fd.real < mpf(H.numerator) / H.denominator - mpf('0.01')
    assert m0 * pi + mpf('0.1') < Fd.imag < (m0 + 1) * pi - mpf('0.1')
    print(f'{name}: |f2| = {float((F[0]**2 + F[1]**2) ** 0.5):.4f}, M3 box = {float(M3b):.4f}, '
          f'a = {float(aQ):.4f}, b = {float(bQ):.4f}, H = {float(Fd.real):.6f}, '
          f'Im Fd/pi = {float(Fd.imag / pi):.4f}; boxes {len(ray)} {len(hor)} {len(ver)}')
    fields = [
        ('ur', lean_rat(ur)), ('ui', lean_rat(ui)), ('vr', lean_rat(vr)), ('vi', lean_rat(vi)),
        ('x1', lean_rat(x1)), ('rho', lean_rat(rho)), ('Y', lean_rat(Y)), ('V', lean_rat(V)),
        ('m', lean_rat(m)), ('M3', lean_rat(M3)), ('c', lean_rat(c_ray)), ('H', lean_rat(H)),
        ('m0', f'({m0} : ℤ)'), ('prec', str(prec)),
        ('rayL', lean_list([b for _, b in ray[:-1]])), ('rayB', lean_rat(ray[-1][1])),
        ('horL', lean_list([b for _, b in hor[:-1]])), ('horB', lean_rat(hor[-1][1])),
        ('verA', lean_rat(ver[0][0])), ('verL', lean_list([b for _, b in ver[:-1]])),
    ]
    body = '\n'.join(f'  {k} := {v}' for k, v in fields)
    return f'/-- The certificate data for case ({name}). -/\ndef data{name} : SData where\n{body}\n'


if __name__ == '__main__':
    D = json.load(open(os.path.join(HERE, 'saddle_data.json')))
    parts = [make('A', D['A'], V=Fr(10001, 10000), m=Fr(1, 2), M3=Fr(1, 10), c_ray=Fr(1, 5),
                  H=Fr(-939), m0=-16),
             make('B', D['B'], V=Fr(1), m=Fr(4, 5), M3=Fr(3, 10), c_ray=Fr(1, 5),
                  H=Fr(-1175), m0=-13)]
    head = ('import OddZeta.Cert.Machinery\n\n'
            '/-!\n# Data of the saddle-point certificates\n\n'
            'Generated by `scripts/saddle_lean_data.py` from `scripts/saddle_data.json`.\n-/\n\n'
            'set_option linter.style.longLine false\n\n'
            'namespace OddZeta.Cert\n\n')
    open(OUT, 'w').write(head + '\n'.join(parts) + '\nend OddZeta.Cert\n')
    print('wrote', os.path.normpath(OUT))
