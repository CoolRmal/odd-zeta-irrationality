"""Per-r certificate data for the family eta^(r), 3 <= r <= 299 odd (OddZeta/Family/Small*.lean).

For each r: the saddle u* (mpmath), a rational approximation ut, v, the path
  -i oo -> P_R = 20 + i yR -> bot -> sigma -> top -> P_L -> -2,
and grids for the three segments, chosen by a floating-point emulation of the Lean checker
`famCertOK` (OddZeta/Family/SmallMach.lean) with safety margins.  Output: small_cert_data.json.
"""
import cmath, json, math, os, sys
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, findroot
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

mp.dps = 50
CB = [(0, -1), (150, 1), (45, 1), (105, -1), (48, 1), (102, -1), (50, 1), (100, -1), (53, 1), (97, -1),
      (56, 1), (94, -1), (60, 1), (90, -1)]
RHO = Fr(1, 10 ** 10)
KG = -90 * math.log(45) + 54 * math.log(54) + 50 * math.log(50) + 44 * math.log(44) + 38 * math.log(38) \
    + 30 * math.log(30)
MARGIN = 0.1           # absolute safety margin in the emulated inequalities


# ---------------------------------------------------------------- high precision functions
def mg1(u): return sum(c * mp.log(b + u) for b, c in CB)
def me1(u): return mp.log(74 + u) - mp.log(76 + u)
def mg2(u): return sum(c / (b + u) for b, c in CB)
def me2(u): return 1 / (74 + u) - 1 / (76 + u)
def mF1(r, u): return r * mg1(u) + me1(u) - 2j * mp.pi
def mF2(r, u): return r * mg2(u) + me2(u)


def saddles(rs):
    a = findroot(mg1, mpf('4.19'))
    D = -mg2(a)
    out, start = {}, None
    for r in sorted(rs, reverse=True):
        guess = start if start is not None else a - 2j * mp.pi / (r * D)
        u = findroot(lambda u: mF1(r, u), mpc(guess))
        for _ in range(5):
            u = u - mF1(r, u) / mF2(r, u)
        out[r] = u
        start = u
    return out


# ---------------------------------------------------------------- float point evaluation (Phi = r g + e - 2 pi i u)
def xl(w): return w * cmath.log(w)


def Pt(r, x, y):
    """(Re Phi, Im Phi, Phi') at x + i y (float)."""
    u = complex(x, y)
    g = sum(c * xl(b + u) for b, c in CB) + KG
    e = xl(74 + u) - xl(76 + u) + 2 * math.log(2)
    g1 = sum(c * cmath.log(b + u) for b, c in CB)
    e1 = cmath.log(74 + u) - cmath.log(76 + u)
    F = r * g + e - 2j * math.pi * u
    F1 = r * g1 + e1 - 2j * math.pi
    return F.real, F.imag, F1


# ---------------------------------------------------------------- box bounds (exact mirror of Num.lean)
def lowAbs(a, b): return max(a, -b, 0)
def lowN(xl_, xh, yl, yh): return max(lowAbs(xl_, xh), lowAbs(yl, yh))
def okBox(xl_, xh, yl, yh): return 0 < xl_ or yh < 0 or 0 < yl


def F2Box(r, xl_, xh, yl, yh):
    g = sum(abs(c) / lowN(b + xl_, b + xh, yl, yh) for b, c in CB)
    e = 2 / (lowN(74 + xl_, 74 + xh, yl, yh) * lowN(76 + xl_, 76 + xh, yl, yh))
    return r * g + e


# directions (a, b), a^2 + b^2 <= 1, for normLo
DIRS = [(Fr(1), Fr(0)), (Fr(0), Fr(1)), (Fr(7071, 10000), Fr(7071, 10000)), (Fr(9238, 10000), Fr(3826, 10000)),
        (Fr(3826, 10000), Fr(9238, 10000))]


def normLo(x, y):
    return max(a * abs(x) + b * abs(y) for a, b in DIRS)


def F3Disc(r, x, y, R):
    g = sum(abs(c) / (normLo(b + x, y) - R) ** 2 for b, c in CB)
    e = 1 / (normLo(74 + x, y) - R) ** 2 + 1 / (normLo(76 + x, y) - R) ** 2
    return r * g + e


def F2Q(r, x, y):
    def inv(a, b):
        n = a * a + b * b
        return (a / n, -b / n)
    re = im = Fr(0)
    for b, c in CB:
        q = inv(b + x, y)
        re += r * c * q[0]; im += r * c * q[1]
    q1, q2 = inv(74 + x, y), inv(76 + x, y)
    return re + q1[0] - q2[0], im + q1[1] - q2[1]


# ---------------------------------------------------------------- the segment checker (mirror of SmallSeg.lean)
class Seg:
    def __init__(self, r, ax, ay, ex, ey, rho, T):
        self.r, self.ax, self.ay, self.ex, self.ey, self.rho, self.T = r, ax, ay, ex, ey, float(rho), float(T)
        self.fx, self.fy, self.fex, self.fey = float(ax), float(ay), float(ex), float(ey)
        self.E = abs(self.fex) + abs(self.fey)
        self.cache = {}

    def pt(self, t):
        if t not in self.cache:
            x, y = self.fx + float(t) * self.fex, self.fy + float(t) * self.fey
            self.cache[t] = Pt(self.r, x, y)
        return self.cache[t]

    def piece(self, t, s):
        ft, fs = float(t), float(s)
        xu, yu = self.fx + ft * self.fex, self.fy + ft * self.fey
        xv, yv = self.fx + fs * self.fex, self.fy + fs * self.fey
        rho = self.rho
        xl_, xh, yl, yh = min(xu, xv) - rho, max(xu, xv) + rho, min(yu, yv) - rho, max(yu, yv) + rho
        if not okBox(xl_, xh, yl, yh):
            return False
        h = fs - ft
        if h <= 0:
            return False
        B = F2Box(self.r, xl_, xh, yl, yh)
        K = B * (self.fex ** 2 + self.fey ** 2) / 2
        W = B * rho * (h / 2 * self.E + rho / 2)
        e = complex(self.fex, self.fey)
        Pre, _, P1 = self.pt(t)
        Qre, _, Q1 = self.pt(s)
        DP = (P1 * e).real
        DQ = (Q1 * e).real
        GP = abs(P1.real) + abs(P1.imag)
        GQ = abs(Q1.real) + abs(Q1.imag)
        lP = Pre + max(0, h / 2 * DP + K * (h / 2) ** 2) + rho * GP + W
        lQ = Qre + max(0, h / 2 * -DQ + K * (h / 2) ** 2) + rho * GQ + W
        return lP <= self.T - MARGIN and lQ <= self.T - MARGIN

    def grid(self, tE=Fr(1), stop=None, maxk=16):
        """greedy dyadic grid on [0, tE]; `stop(t)` may end the grid early (returns the grid, end)"""
        t, ts = Fr(0), []
        while True:
            if stop is not None and t > 0 and stop(t):
                return ts, t
            if self.piece(t, tE):
                return ts, tE
            s = None
            for k in range(0, maxk + 1):
                h = Fr(1, 2 ** k)
                cand = (t // h + 1) * h          # next dyadic multiple of h
                if cand >= tE:
                    continue
                if self.piece(t, cand):
                    s = cand
                    break
            if s is None:
                return None, None
            ts.append(s)
            t = s
            if len(ts) > 400:
                return None, None


def lastOK(r, qx, qy, T):
    fqx, fqy = float(qx), float(qy)
    if not (fqy < 0 and fqx < 0):
        return False
    Pre, _, P1 = Pt(r, fqx, fqy)
    ex, ey = -2 - fqx, -fqy
    B = F2Box(r, min(-2, fqx), max(-2, fqx), fqy, 0)
    D = (P1 * complex(ex, ey)).real
    ok1 = Pre + max(0, D + B * (ex ** 2 + ey ** 2) / 2) <= float(T) - MARGIN
    ok2 = Pt(r, -2, 0)[0] <= float(T) - MARGIN
    return ok1 and ok2


# ---------------------------------------------------------------- helpers
def rnd(x, den):
    return Fr(round(float(x) * den), den)


def floorq(x, den):
    return Fr(math.floor(float(x) * den), den)


def ceilq(x, den):
    return Fr(math.ceil(float(x) * den), den)


def design(r, us, s0=1.5):
    ur = Fr(int(mp.nint(mp.re(us) * 10 ** 14)), 10 ** 14)
    ui = Fr(int(mp.nint(mp.im(us) * 10 ** 14)), 10 ** 14)
    F2 = complex(mF2(r, us))
    ph = (math.pi - cmath.phase(F2)) / 2
    ee = cmath.exp(1j * ph)
    if ee.real > 0:
        ee = -ee
    v = s0 * ee
    vr, vi = rnd(v.real, 1000), rnd(v.imag, 1000)
    V = ceilq(math.hypot(float(vr), float(vi)) + 1e-9, 10 ** 6)
    assert V ** 2 >= vr ** 2 + vi ** 2
    R = V + RHO
    # saddle checks
    F2r, F2i = F2Q(r, ur, ui)
    m = floorq(math.hypot(float(F2r), float(F2i)) * (1 - 1e-6), 10 ** 6)
    assert m > 0 and m ** 2 <= F2r ** 2 + F2i ** 2
    assert okBox(ur - R, ur + R, ui - R, ui + R)
    for b, c in CB + [(74, 1), (76, -1)]:
        assert R < normLo(b + ur, ui)
    M3 = ceilq(float(F3Disc(r, ur, ui, R)) * (1 + 1e-6), 10 ** 6)
    assert F3Disc(r, ur, ui, R) <= M3 and M3 * RHO <= m / 2
    aQ = -(F2r * (vr ** 2 - vi ** 2) - F2i * (2 * vr * vi)) / 2
    bQ = aQ - M3 * RHO * (vr ** 2 + vi ** 2) / 2 - M3 * V ** 3 / 6
    assert bQ > Fr(1, 100), (r, float(bQ))
    b = Fr(1, 100)
    # H, alpha
    Hre, Him, F1 = Pt(r, float(ur), float(ui))
    Hm = complex(us.real, us.imag)
    assert abs(F1) < 1e-9, (r, abs(F1))
    T = floorq(Hre - float(b) - 0.1, 1000)
    assert Hre < -(214.8 * r - 3) - 0.01
    utm = mpc(mpf(ur.numerator) / ur.denominator, mpf(ui.numerator) / ui.denominator)
    assert abs(mF1(r, utm)) < float(m) * float(RHO) / 20, (r, abs(mF1(r, utm)))
    assert ui - vi + RHO < 0 and ui + vi + RHO < 0
    m0 = math.floor(Him / math.pi)
    dist = min(Him - m0 * math.pi, (m0 + 1) * math.pi - Him)
    assert dist > 1e-3, (r, dist)
    # bot, top approximations
    bot, top = (ur - vr, ui - vi), (ur + vr, ui + vi)
    br, bi = rnd(bot[0], 10 ** 6), rnd(bot[1], 10 ** 6)
    tr, ti = rnd(top[0], 10 ** 6), rnd(top[1], 10 ** 6)
    rs = Fr(2, 10 ** 6)
    assert abs(bot[0] - br) + abs(bot[1] - bi) + RHO <= rs and abs(top[0] - tr) + abs(top[1] - ti) + RHO <= rs
    # P_L
    plx, ply = rnd((float(tr) - 2) / 2, 10 ** 6), rnd(float(ti) / 2, 10 ** 6)
    # ray: yR
    best = None
    for yR in ([Fr(-1, 4)] + ([floorq(float(bi), 10 ** 4)] if float(bi) < -0.25 else [])):
        if not (r * Fr(-2400670, 10000) + Fr(-97210, 10000) + 6 * yR <= T):
            continue
        sR = Seg(r, Fr(20), yR, br - 20, bi - yR, rs, T)
        gR, _ = sR.grid()
        if gR is None:
            continue
        if best is None or len(gR) < len(best[1]):
            best = (yR, gR)
    assert best is not None, (r, 'ray/PR segment')
    yR, gR = best
    sT = Seg(r, tr, ti, plx - tr, ply - ti, rs, T)
    gT, _ = sT.grid()
    assert gT is not None, (r, 'top-PL')
    sL = Seg(r, plx, ply, -2 - plx, -ply, 0, T)

    def stop(t):
        qx, qy = plx + t * (-2 - plx), ply + t * (-ply)
        return lastOK(r, qx, qy, T)
    gL, lam = sL.grid(tE=Fr(1), stop=stop)
    assert gL is not None and lam < 1, (r, 'PL-(-2)')
    gL = gL[:-1] if gL and gL[-1] == lam else gL   # the grid on [0, lam] has interior points gL
    assert sL.grid is not None
    # re-verify the chain on [0, lam] with end lam
    chain = [Fr(0)] + gL + [lam]
    assert all(sL.piece(chain[i], chain[i + 1]) for i in range(len(chain) - 1))
    # geometry
    rho = RHO
    dnorm = math.hypot(float(plx) + 2, float(ply))
    na = Fr(math.ceil(float(ply) / dnorm * 10 ** 6), 10 ** 6)          # negative, rounded towards 0
    nb = Fr(math.trunc(-(float(plx) + 2) / dnorm * 10 ** 6), 10 ** 6)
    assert na ** 2 + nb ** 2 <= 1 and na < 0
    c0cands = [-yR, -(ui - vi + rho), -(ui + vi + rho), -ply, na * plx + nb * ply, -2 * na, Fr(2)]
    c0 = floorq(float(min(c0cands)) * 0.999, 10 ** 5)
    assert c0 > 0 and all(c0 <= c for c in c0cands)
    Kc = [20 / (-yR), (ur - vr + rho) / (-(ui - vi + rho)), (ur + vr + rho) / (-(ui + vi + rho)), plx / (-ply), Fr(0)]
    K = ceilq(float(max(Kc)) + 1e-3, 1000)
    assert 20 + K * yR <= 0 and (ur - vr + rho) + K * (ui - vi + rho) <= 0 and \
        (ur + vr + rho) + K * (ui + vi + rho) <= 0 and plx + K * ply <= 0
    assert -40 <= ur - vr - rho and -40 <= ur + vr - rho and -40 <= plx
    return dict(r=r, ur=ur, ui=ui, vr=vr, vi=vi, V=V, m=m, M3=M3, b=b, T=T, m0=m0, yR=yR, br=br, bi=bi,
                tr=tr, ti=ti, rs=rs, plx=plx, ply=ply, lam=lam, gR=gR, gT=gT, gL=gL, c0=c0, na=na, nb=nb, K=K,
                H=Hre, dist=dist)


def lean_rat(q):
    q = Fr(q)
    if q.denominator == 1:
        return f'({q.numerator} : ℚ)'
    return f'mkRat ({q.numerator}) {q.denominator}'


def lean_list(l):
    return '[' + ', '.join(lean_rat(x) for x in l) + ']'


FIELDS = ['ur', 'ui', 'vr', 'vi', 'V', 'm', 'M3', 'b', 'T', 'm0', 'yR', 'br', 'bi', 'tr', 'ti', 'rs', 'plx', 'ply',
          'lam', 'gR', 'gT', 'gL', 'c0', 'na', 'nb', 'K']


def lean_record(d):
    lines = [f'/-- The certificate data for `r = {d["r"]}`. -/', f'def d{d["r"]} : SmData where']
    for k in FIELDS:
        v = d[k]
        if k == 'm0':
            val = f'({v} : ℤ)'
        elif isinstance(v, list):
            val = lean_list(v)
        else:
            val = lean_rat(v)
        lines.append(f'  {k} := {val}')
    return '\n'.join(lines)


HEADER = """import OddZeta.Family.SmallMach

/-!
# Per-`r` certificate data and kernel checks, chunk {k}: `r ∈ {{{rs}}}`

Generated by `scripts/small_cert_gen.py`.
-/

set_option linter.style.longLine false

namespace OddZeta.Small

"""


def write_chunks(designs, per_chunk, outdir):
    chunks = [designs[i:i + per_chunk] for i in range(0, len(designs), per_chunk)]
    names = []
    for k, ch in enumerate(chunks, 1):
        rs = ', '.join(str(d['r']) for d in ch)
        body = HEADER.format(k=k, rs=rs)
        for d in ch:
            body += lean_record(d) + '\n\n'
        body += f'/-- The data of chunk {k}. -/\n'
        body += f'def chunk{k} : List (ℕ × SmData) :=\n  [' + ', '.join(f'({d["r"]}, d{d["r"]})' for d in ch) + ']\n\n'
        body += f'theorem chunk{k}_ok : chunk{k}.all (fun p => famCertOK p.1 p.2) = true := by\n  decide +kernel\n\n'
        body += 'end OddZeta.Small\n'
        with open(os.path.join(outdir, f'SmallChk{k}.lean'), 'w') as f:
            f.write(body)
        names.append(k)
    return names


if __name__ == '__main__':
    rs = list(range(3, 300, 2))
    per_chunk = 15
    args = sys.argv[1:]
    test = False
    if args and args[0] == '--test':
        test = True
        args = args[1:]
    if args:
        rs = [int(a) for a in args]
    S = saddles(sorted(set(rs) | set(range(rs[0], 300, 2))))
    out, designs = [], []
    tot = 0
    for r in rs:
        d = design(r, S[r])
        designs.append(d)
        n = len(d['gR']) + len(d['gT']) + len(d['gL']) + 3 + 3
        tot += n
        print(r, 'yR', float(d['yR']), 'grid', len(d['gR']), len(d['gT']), len(d['gL']), 'lam', float(d['lam']),
              'H', round(d['H'], 2), 'dist', round(d['dist'], 3), 'c0', float(d['c0']), 'K', float(d['K']), flush=True)
        out.append({k: (str(v) if isinstance(v, Fr) else ([str(x) for x in v] if isinstance(v, list) else v))
                    for k, v in d.items()})
    print('total point evaluations ~', tot)
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, 'small_cert_data.json'), 'w') as f:
        json.dump(out, f, indent=0)
    if test:
        with open(os.path.join(here, '..', 'scratch', 'SmallTest.lean'), 'w') as f:
            f.write(HEADER.format(k=0, rs=', '.join(map(str, rs))))
            for d in designs:
                f.write(lean_record(d) + '\n\n')
                f.write(f'theorem ok{d["r"]} : famCertOK {d["r"]} d{d["r"]} = true := by\n  decide +kernel\n\n')
            f.write('end OddZeta.Small\n')
    else:
        write_chunks(designs, per_chunk, os.path.join(here, '..', 'OddZeta', 'Family'))
