"""Region sets (rectangles B_L, B_R, points P_L, P_R, x0, lower ray at x_R) for ranges of r.
Sup of Re g and of Re e + 2 pi Im u over each piece (rectangles: boundary, by the maximum principle)."""
from mpmath import mp, mpf, mpc, pi, exp, arg, linspace
from family import g, e, g2, e2, Fs, saddle_family
mp.dps = 20

def reG(u): return g(u).real
def reE(u): return (e(u) - 2j * pi * u).real          # Re e + 2 pi Im u

def seg_max(fun, A, B, N=400):
    return max(fun(A + (B - A) * mpf(i) / N) for i in range(N + 1))

def rect_max(fun, x1, x2, y1, y2, N=300):
    c = [mpc(x1, y1), mpc(x2, y1), mpc(x2, y2), mpc(x1, y2)]
    return max(seg_max(fun, c[i], c[(i + 1) % 4], N) for i in range(4))

def ray_max(fun, x, y0, Y=200, N=800):
    return max(fun(mpc(x, -y0 - (Y - y0) * mpf(i) / N)) for i in range(N + 1))

def pieces(RS):
    (xl1, xl2, yl), (xr1, xr2, yr), (PL, PR, x0, xR) = RS['BL'], RS['BR'], RS['pts']
    out = []
    for fun in (reG, reE):
        out.append((rect_max(fun, xl1, xl2, yl, 0), rect_max(fun, xr1, xr2, yr, 0), seg_max(fun, PL, mpc(x0, 0)),
                    ray_max(fun, xR, -PR.imag), ))
    return list(zip(*out))  # rows (Sg, Se)

def check_range(rs, RS, S):
    rows = pieces(RS)
    res = []
    for r in rs:
        u = S[r]
        F2 = r * g2(u) + e2(u)
        ph = (pi - arg(F2)) / 2
        ee = exp(1j * ph)
        if ee.real > 0: ee = -ee
        s0 = RS['s0']
        top, bot = u + s0 * ee, u - s0 * ee
        (xl1, xl2, yl), (xr1, xr2, yr), _ = RS['BL'], RS['BR'], RS['pts']
        inL = xl1 <= top.real <= xl2 and yl <= top.imag < 0
        inR = xr1 <= bot.real <= xr2 and yr <= bot.imag < 0
        Hd = Fs(r, u).real; delta = abs(F2) * s0 ** 2 / 8
        m = min(Hd - delta - (r * Sg + Se) for Sg, Se in rows)
        res.append((r, inL, inR, float(m), complex(top), complex(bot)))
    return rows, res

if __name__ == '__main__':
    rs = list(range(3, 52, 2))
    S = saddle_family(rs)
    for r in rs:
        u = S[r]
        F2 = r * g2(u) + e2(u); ph = (pi - arg(F2)) / 2; ee = exp(1j * ph)
        if ee.real > 0: ee = -ee
        print(r, f'u*={complex(u):.3f} dir={complex(ee):.3f} top(1.5)={complex(u+1.5*ee):.3f} bot={complex(u-1.5*ee):.3f}')
