"""Generate the Lean certificates `OddZeta/Phi/DataA.lean`, `OddZeta/Phi/DataB.lean` for the
lower bound of `φ(x) = min_y φ₀(x, y)` and cross-check them against `phi.py`.

The certificate is the list `X` of breakpoints (from `phi.breakpoints`) and the values
`vals[i] = φ` on `(X[i], X[i+1])` (from `phi.phi` at the midpoint).  This script also simulates
the Lean checker `OddZeta.PhiCert.checkPhiCert` (same algorithm, same integer arithmetic) and
verifies that for every interval the checker's lower bound equals `vals[i]`.

It also computes the chunk values of the fixed-point lower bound `OddZeta.PhiCert.sumLB` for
`OddZeta.phiSum` (module `Sum.lean`; scale 10^9, K = 20, m = m̂) and compares with the exact
rational value.

Usage: python3 phi_cert.py            (writes ../OddZeta/Phi/Data{A,B}.lean, ~45 s)
"""
from fractions import Fraction as Fr
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from params import CASES  # noqa: E402
from phi import phi, breakpoints, mhat  # noqa: E402

DATA = {
    'A': dict(eta0=196, zs=[58, 58, 58, 59, 60],
              ps=[62, 62, 63, 64, 64, 65, 66, 66, 68, 69, 70, 72, 73, 75, 76, 77, 79, 80], mhat=72),
    'B': dict(eta0=151, zs=[46] * 7,
              ps=[47, 47, 48, 49, 49, 49, 50, 51, 51, 51, 52, 53, 53, 53, 54, 55, 55, 55, 56, 57, 57,
                  57, 58, 59, 59, 59, 60, 61], mhat=57),
}

KEYB = 1024  # key = (a * nα % dα) * KEYB + a
CHUNK = 100  # intervals per kernel chunk (`OddZeta.PhiCert.chunkB + 1`)


def terms(e0, zs, ps):
    """Atoms (a, cp, cn, l, e, r) as in `OddZeta.PhiCert.terms`; their values sum to
    phi0(x, t) + len(zs) for t in [0, 1)."""
    t = []
    for h in zs:
        t += [(h, 0, 1, 1, 0, 0), (e0, 1, 0, 1, 1, 0), (e0 - h, 0, 1, 0, 0, 1)]
    for h in ps:
        t += [(e0 - 2 * h, 1, 0, 0, 0, 0), (h, 1, 0, 1, 0, 0), (e0 - h, 0, 1, 0, 0, 1)]
    return t


def dedup(l):
    # Mathlib `List.dedup` keeps the last occurrence
    out = []
    for i, a in enumerate(l):
        if a not in l[i + 1:]:
            out.append(a)
    return out


def atoms(e0, zs, ps):
    ts = terms(e0, zs, ps)
    L = dedup([t[0] for t in ts])
    at = []
    for a in L:
        w = [sum(t[j] for t in ts if t[0] == a) for j in range(1, 6)]
        cp, cn = w[0], w[1]
        at.append((a, max(cp - cn, 0), max(cn - cp, 0), w[2], w[3], w[4]))
    atF = [c for c in at if c[3] + c[4] + c[5] == 0]
    atS = [c for c in at if c[3] + c[4] + c[5] != 0]
    return atF, atS


def sweep(ws):
    s, m = 0, 0
    for (l, e, r) in reversed(ws):
        s, m = l + s, min(l + s, e + s, r + m)
    return s, m


def check(e0, zs, ps, X, vals, stats=None):
    """Simulate `checkPhiCert` (the chunk restarts do not change the result).  Returns the list
    of failing intervals (should be empty) and checks that the bound is exactly `vals[i]`."""
    assert all(h <= e0 for h in zs) and all(2 * h <= e0 for h in ps)
    assert X[0] == 0 and X[-1] == 1 and len(vals) + 1 == len(X)
    atF, S = atoms(e0, zs, ps)
    off = len(zs)
    bad = []
    ncmp = 0
    ord_ = S
    for i in range(len(vals)):
        if i % CHUNK == 0:
            ord_ = S
        al, be, v = X[i], X[i + 1], vals[i]
        na, da, nb, db = al.numerator, al.denominator, be.numerator, be.denominator
        ok = na >= 0 and na * db < nb * da
        fp = fn = 0
        for (a, cp, cn, l, e, r) in atF:
            k = a * na // da
            ok &= a * nb <= k * db + db
            fp += cp * k
            fn += cn * k
        ents = []
        for c in ord_:
            a = c[0]
            P = a * na
            k = P // da
            ents.append(dict(key=(P % da) * KEYB + a, k=k, r=P % da, w=a * nb, kd=k * db, c=c))
        srt = []
        for e in reversed(ents):   # sortE = foldr insE
            j = 0
            while j < len(srt) and not (e['key'] <= srt[j]['key']):
                j += 1
                ncmp += 1
            ncmp += 1
            srt.insert(j, e)
        for e in srt:
            ok &= e['w'] <= e['kd'] + db
        for e, f in zip(srt, srt[1:]):
            a, b = e['c'][0], f['c'][0]
            if a < b:
                ok &= e['r'] <= f['r']
            elif b < a:
                ok &= e['w'] + f['kd'] <= f['w'] + e['kd']
            else:
                ok = False
        cps = sum(e['c'][1] * e['k'] for e in srt)
        cns = sum(e['c'][2] * e['k'] for e in srt)
        s, m = sweep([(e['c'][3], e['c'][4], e['c'][5]) for e in srt])
        lb = fp + cps + m - (off + fn + cns)   # checker: v + off + fn + cns <= fp + cps + m
        if not ok or lb < v:
            bad.append((i, al, be, v, lb, ok))
        elif lb != v:
            bad.append((i, al, be, v, lb, 'bound larger than phi ?!'))
        ord_ = [e['c'] for e in srt]
    if stats is not None:
        stats['sort comparisons'] = ncmp
        stats['floor-only atoms'] = len(atF)
        stats['sweep atoms'] = len(S)
    return bad


SUM_S = 10 ** 9  # fixed-point scale of `OddZeta.PhiCert.sumLB`
SUM_K = 20


def term_lb(S, m, K, na, da, nb, db):
    """`OddZeta.PhiCert.termLB` (natural-number arithmetic)."""
    num = S * max(da * nb - db * na, 0)
    t = sum(num // ((k * da + na) * (k * db + nb)) for k in range(1, K + 1))
    if da <= m * na:
        t += num // (na * nb)
    return t


def sum_chunks(m, X, vals, S=SUM_S, K=SUM_K, C=CHUNK):
    """Values of `sumChunk S m K C X vals j` for all chunks j."""
    out = []
    for j in range(0, len(vals), C):
        t = 0
        for i in range(j, min(j + C, len(vals))):
            a, b = X[i], X[i + 1]
            t += vals[i] * term_lb(S, m, K, a.numerator, a.denominator, b.numerator, b.denominator)
        out.append(t)
    return out


def phisum_exact(m, K, X, vals):
    tot = Fr(0)
    for i in range(len(vals)):
        a, b = X[i], X[i + 1]
        s = sum(Fr(1) / (k + a) - Fr(1) / (k + b) for k in range(1, K + 1))
        if Fr(1, m) <= a:
            s += 1 / a - 1 / b
        tot += vals[i] * s
    return tot


def lean_list(items, per_line=8, indent='  '):
    lines = []
    for j in range(0, len(items), per_line):
        lines.append(indent + ', '.join(items[j:j + per_line]))
    return '[\n' + ',\n'.join(lines) + ']'


def write_lean(name, d, X, vals, chunks_sum):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'OddZeta', 'Phi',
                        f'Data{name}.lean')
    e0, zs, ps = d['eta0'], d['zs'], d['ps']
    xs = [f'({x.numerator}, {x.denominator})' for x in X]
    vs = [str(v) for v in vals]
    nch = (len(vals) + CHUNK - 1) // CHUNK   # chunks 0 .. nch - 1
    N = nch - 1
    assert len(vals) <= N * CHUNK + CHUNK - 1
    chunks = '\n'.join(
        f'theorem check{name}_chunk_{j} : chunkOK {e0} zs{name} ps{name} X{name} vals{name} {j} = true := by\n'
        f'  decide +kernel\n' for j in range(nch))
    cases = '\n'.join(f'    | {j}, _ => check{name}_chunk_{j}' for j in range(nch))
    out = f'''import OddZeta.Phi.Check

/-!
# φ certificate, case {name}

Generated by `scripts/phi_cert.py` (do not edit).  `X{name}` is the list of breakpoints
(`phi.breakpoints`, {len(X)} points) and `vals{name}[i]` the exact value of `φ` on
`(X{name}[i], X{name}[i+1])` (`phi.phi` at the midpoint).  The check is split into {nch} kernel
computations of {CHUNK} intervals each (`chunkOK`), assembled by `checkPhiCert_of_chunks`.
-/

namespace OddZeta.PhiCert

/-- Zero-block directions, case {name}. -/
def zs{name} : List ℕ := {[*zs]}

/-- Pole-block directions, case {name}. -/
def ps{name} : List ℕ := {lean_list([str(h) for h in ps], 20)}

/-- Breakpoints as (numerator, denominator) pairs. -/
def X{name}raw : List (ℕ × ℕ) := {lean_list(xs, 8)}

/-- The breakpoints `X{name}` (strictly increasing, from `0` to `1`). -/
def X{name} : List ℚ := X{name}raw.map fun p => mkRat p.1 p.2

/-- The values of `φ` on the intervals of `X{name}`. -/
def vals{name} : List ℕ := {lean_list(vs, 24)}

/-- The chunk values `sumChunk {SUM_S} {d['mhat']} {SUM_K} {CHUNK} X{name} vals{name} j` of the fixed-point
lower bound for `phiSum` (checked in `Sum.lean`). -/
def sumChunks{name} : List ℕ := {lean_list([str(v) for v in chunks_sum], 5)}

{chunks}
/-- The certificate for case {name} is valid. -/
theorem check{name} : checkPhiCert {e0} zs{name} ps{name} X{name} vals{name} = true :=
  checkPhiCert_of_chunks (by decide +kernel) {N} (by decide +kernel) fun j hj =>
    match j, hj with
{cases}
    | _ + {nch}, h => absurd h (by omega)

end OddZeta.PhiCert
'''
    open(path, 'w').write(out)
    return path


def main():
    for name in 'AB':
        d = DATA[name]
        c = CASES[name]
        assert c['eta0'] == d['eta0'] and c['eta'] == d['zs'] + d['ps'] and len(d['zs']) == c['r']
        assert mhat(c)[1][-1] == d['mhat'] and mhat(c)[0] == d['mhat']
        X = breakpoints(c)
        vals = [phi(c, (X[i] + X[i + 1]) / 2) for i in range(len(X) - 1)]
        st = {}
        bad = check(d['eta0'], d['zs'], d['ps'], X, vals, st)
        print(name, 'intervals', len(vals), 'max phi', max(vals), 'failures', len(bad), st)
        for b in bad[:20]:
            print('   ', b)
        ch = sum_chunks(d['mhat'], X, vals)
        ex = phisum_exact(d['mhat'], SUM_K, X, vals)
        lo = sum(ch)
        print('  phiSum: fixed-point lower bound', lo / SUM_S, 'exact', float(ex),
              'sound', lo <= SUM_S * ex, 'chunks', len(ch))
        print('  wrote', write_lean(name, d, X, vals, ch))


if __name__ == '__main__':
    main()
