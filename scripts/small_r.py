"""Per-r path certificates for small r: margins and adaptive grid sizes (Lemma 4.8 style)."""
from mpmath import mp, mpf, mpc, pi, exp, arg, fabs
from family import g, e, g1, e1, g2, e2, Fs, F1s, saddle_family, CB
mp.dps = 20
EB = [(74, 1), (76, -1)]

def H(r, u): return Fs(r, u).real
def dH(r, u): return abs(F1s(r, u))          # |grad H| = |F'|
def B2(r, u, rad):                            # bound for |F''| on a disc of radius rad around u
    return r * sum(abs(c) / max(abs(b + u) - rad, mpf('1e-9')) ** 2 for b, c in CB) + sum(abs(c) / (abs(b + u) - rad) ** 2 for b, c in EB)

def seg_cost(r, A, B, theta):
    """number of adaptive grid points needed to certify H <= theta on [A,B]; returns (points, min slack)"""
    L = abs(B - A); s = mpf(0); n = 0; minsl = mpf(10) ** 9
    while s < L:
        u = A + (B - A) * s / L
        sl = theta - H(r, u)
        minsl = min(minsl, sl)
        if sl <= 0: return None, float(sl)
        # step h with (h/2)(|F'| + (h/2) B2) <= sl
        b2 = B2(r, u, mpf(1)); fp = dH(r, u)
        h = min(mpf(1), 2 * sl / (fp + 1e-9), (sl / b2) ** 0.5 * 2)
        h = max(h, mpf('1e-6'))
        s += h; n += 1
    return n, float(minsl)

def plan(r, u, s0, s1=1, variant='A', xR=20, yc=mpf('0.25'), x0=-2, Y=200):
    F2 = r * g2(u) + e2(u); ph = (pi - arg(F2)) / 2; ee = exp(1j * ph)
    if ee.real > 0: ee = -ee
    top, bot = u + s0 * ee, u - s0 * ee
    Hd = H(r, u); delta = abs(F2) * s0 ** 2 / 8; theta = Hd - delta
    if variant == 'A':
        ext = u - (s0 + s1) * ee
        pieces = [(ext, bot), (top, mpc(x0, 0)), (ext, mpc(ext.real, -Y))]
    else:
        PR = mpc(xR, -yc); PL = mpc(top.real - 0.3, -yc)
        pieces = [(PR, bot), (top, PL), (PL, mpc(x0, 0)), (PR, mpc(xR, -Y))]
    out = []
    for A, B in pieces:
        n, sl = seg_cost(r, A, B, theta)
        out.append((n, round(sl, 3)))
    return out

if __name__ == '__main__':
    rs = list(range(3, 50, 2))
    S = saddle_family(rs)
    for r in rs:
        u = S[r]
        best = None
        for s0 in [mpf('1.5'), mpf('1.2'), mpf(1), mpf('0.8'), mpf('0.6')]:
            for var in 'AB':
                p = plan(r, u, s0, variant=var)
                if all(n is not None for n, _ in p):
                    tot = sum(n for n, _ in p)
                    if best is None or tot < best[0]:
                        best = (tot, float(s0), var, p)
        print(r, best, flush=True)
