from regions import *
from family import CB
import per_r
mp.dps = 20

def make_RS(rs, S, s0, yc=mpf('0.25'), xR=mpf(20), x0=mpf(-2), pad=mpf('0.03')):
    tops, bots = [], []
    for r in rs:
        u = S[r]; F2 = r * g2(u) + e2(u); ph = (pi - arg(F2)) / 2; ee = exp(1j * ph)
        if ee.real > 0: ee = -ee
        tops.append(u + s0 * ee); bots.append(u - s0 * ee)
    xl1 = min(t.real for t in tops) - pad; xl2 = max(t.real for t in tops) + pad; yl = min(t.imag for t in tops) - pad
    xr1 = min(b.real for b in bots) - pad; yr = min(b.imag for b in bots) - pad
    yc = min(yc, -max(t.imag for t in tops) * 0 + yc)
    return dict(BL=(xl1, xl2, yl), BR=(xr1, xR, yr), pts=(mpc(xl1, -yc), mpc(xR, -yc), x0, xR), s0=s0)

rs_all = list(range(9, 52, 2))
S = saddle_family(rs_all)
for rng, s0 in [((41, 49), 1.5), ((33, 39), 1.5), ((25, 31), 1.4), ((19, 23), 1.3), ((15, 17), 1.2), ((11, 13), 1.0), ((9, 9), 0.9)]:
    rs = list(range(rng[0], rng[1] + 1, 2))
    RS = make_RS(rs, S, mpf(s0))
    rows, res = check_range(rs, RS, S)
    s2 = []
    for r in rs:
        c = per_r.check(r, S[r], dict(per_r.PAPER, s0=mpf(s0)))
        s2.append(round(c['S2'], 3))
    print(rng, 's0', s0, 'BL', [round(float(x), 3) for x in RS['BL']], 'BR', [round(float(x), 3) for x in RS['BR']],
          'rows Sg', [round(float(a), 2) for a, b in rows])
    print('    margins', [(r, round(m, 3)) for r, _, _, m, _, _ in res], 'S2', s2)
