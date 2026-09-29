"""Grids for the kernel-checked region bounds of Lemma 8.7 (OddZeta/Family/RegionsCert.lean).

Mirrors `OddZeta.FamNum.pieceOK` / `chkSeg` / `chkRect` (OddZeta/Family/Num.lean): on a segment
A + [0,1] e, the piece [t, s] (h = s - t) passes if, with B = bound for |Phi''| on the bounding box
of the piece and K = B |e|^2 / 2,
    Re Phi(u_t) + max(0, h/2 * Re(Phi'(u_t) e) + K (h/2)^2) <= T   and
    Re Phi(u_s) + max(0, -h/2 * Re(Phi'(u_s) e) + K (h/2)^2) <= T.
Grids are built greedily (dyadic parameters) with a safety margin MARGIN for the interval
enclosures. Prints the Lean lists `[mkRat a b, ...]`.
"""
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, log, pi

mp.dps = 30
MARGIN = Fr(1, 10**7)
CB = [(0, -1), (150, 1), (45, 1), (105, -1), (48, 1), (102, -1), (50, 1), (100, -1), (53, 1), (97, -1),
      (56, 1), (94, -1), (60, 1), (90, -1)]
KG = -90*log(45) + 54*log(54) + 50*log(50) + 44*log(44) + 38*log(38) + 30*log(30)


def G(u): return sum(c*(b+u)*log(b+u) for b, c in CB) + KG
def G1(u): return sum(c*log(b+u) for b, c in CB)
def Es(u): return (74+u)*log(74+u) - (76+u)*log(76+u) + 2*log(2) - 2j*pi*u
def Es1(u): return log(74+u) - log(76+u) - 2j*pi


def lowAbs(a, b): return max(a, -b, Fr(0))
def lowN(xl, xh, yl, yh): return max(lowAbs(xl, xh), lowAbs(yl, yh))
def g2Box(xl, xh, yl, yh): return sum(Fr(abs(c))/lowN(b+xl, b+xh, yl, yh) for b, c in CB)
def e2Box(xl, xh, yl, yh): return Fr(2)/(lowN(74+xl, 74+xh, yl, yh)*lowN(76+xl, 76+xh, yl, yh))
def okBox(xl, xh, yl, yh): return xl > 0 or yh < 0 or yl > 0
def okBoxE(xl, xh, yl, yh): return okBox(74+xl, 74+xh, yl, yh)
def mpq(q): return mpf(q.numerator)/q.denominator


def grid(Phi, Phi1, bnd, ok, ax, ay, ex, ey, T):
    E2 = ex*ex + ey*ey
    Tm = mpq(T - MARGIN)

    def pt(t):
        u = mpc(mpq(ax + t*ex), mpq(ay + t*ey))
        return Phi(u).real, (Phi1(u)*mpc(mpq(ex), mpq(ey))).real

    def piece(t, P, s, Q):
        xs = [ax + t*ex, ax + s*ex]; ys = [ay + t*ey, ay + s*ey]
        box = (min(xs), max(xs), min(ys), max(ys))
        if not ok(*box): return False
        h = s - t
        K = mpq(bnd(*box)*E2/2*(h/2)**2)
        return (P[0] + max(0, mpq(h/2)*P[1] + K) <= Tm) and (Q[0] + max(0, -mpq(h/2)*Q[1] + K) <= Tm)

    t, P, ts, h = Fr(0), pt(Fr(0)), [], Fr(1)
    while t < 1:
        h = min(h*4, 1 - t)
        while True:
            s = t + h
            Q = pt(s)
            if piece(t, P, s, Q): break
            h /= 2
            if h < Fr(1, 2**30): raise Exception('grid fails at t = %s' % t)
        ts.append(s); t, P = s, Q
    return ts[:-1]


def lean(ts): return '[' + ', '.join('mkRat %d %d' % (q.numerator, q.denominator) for q in ts) + ']'


xL, xL2, yL = Fr(2092953, 10**6), Fr(2702953, 10**6), Fr(-523633, 10**6)
xR, xR2, yR = Fr(5604839, 10**6), Fr(20), Fr(-827198, 10**6)
TG = dict(BL=Fr(-2322435, 10**4), BR=Fr(-2321627, 10**4), PL=Fr(-2325535, 10**4), ray=Fr(-2400670, 10**4))
TE = dict(BL=Fr(-93025, 10**4), BR=Fr(-93914, 10**4), PL=Fr(-91937, 10**4))
THQ = Fr(63, 64)   # the grid on [P_L, -2] for g stops at P_L + THQ (-2 - P_L)

if __name__ == '__main__':
    for name, (x1, x2, y1) in [('BL', (xL, xL2, yL)), ('BR', (xR, xR2, yR))]:
        y2 = Fr(0)
        for fn, Phi, Phi1, bnd, ok, T in [('G', G, G1, g2Box, okBox, TG[name]),
                                          ('E', Es, Es1, e2Box, okBoxE, TE[name])]:
            edges = dict(B=(x1, y1, x2-x1, Fr(0)), T=(x1, y2, x2-x1, Fr(0)), L=(x1, y1, Fr(0), y2-y1),
                         R=(x2, y1, Fr(0), y2-y1))
            for k in 'BTLR':
                print('%s %s %s:' % (name, fn, k), lean(grid(Phi, Phi1, bnd, ok, *edges[k], T)))
    ex, ey = Fr(-2) - xL, Fr(1, 4)
    print('PL E:', lean(grid(Es, Es1, e2Box, okBoxE, xL, Fr(-1, 4), ex, ey, TE['PL'])))
    print('PL G:', lean(grid(G, G1, g2Box, okBox, xL, Fr(-1, 4), THQ*ex, THQ*ey, TG['PL'])))
    print('ray G:', lean(grid(G, G1, g2Box, okBox, Fr(20), Fr(-1, 4), Fr(0), Fr(-647, 4), TG['ray'])))
    # the last piece [Q, -2) of [P_L, -2] (one-sided from Q, `chk_PL_last`), and the point -2
    qx, qy = xL + THQ*ex, Fr(-1, 4) + THQ*ey
    u = mpc(mpq(qx), mpq(qy)); l = 1 - THQ
    B = g2Box(Fr(-2), qx, qy, Fr(0))
    val = G(u).real + max(0, mpq(l)*(G1(u)*mpc(mpq(ex), mpq(ey))).real + mpq(B*(ex*ex + ey*ey)/2*l*l))
    print('last piece: Q = %s + %s i, bound %.6f, value at -2: %.6f (target %.4f)'
          % (qx, qy, float(val), float(G(mpc(-2, 0)).real), float(TG['PL'])))
    ee = (74 + mpc(20, -0.25))*log(74 + mpc(20, -0.25)) - (76 + mpc(20, -0.25))*log(76 + mpc(20, -0.25))
    print('Re e(20 - i/4) = %.6f (target -9.7210)' % float((ee + 2*log(2)).real))
