"""Fast (float) estimate of per-r path certificates for small r."""
import cmath, math
from family import saddle_family
CB = [(0, -1), (150, 1), (45, 1), (105, -1), (48, 1), (102, -1), (50, 1), (100, -1), (53, 1), (97, -1),
      (56, 1), (94, -1), (60, 1), (90, -1)]
EB = [(74, 1), (76, -1)]
KG = -90 * math.log(45) + 54 * math.log(54) + 50 * math.log(50) + 44 * math.log(44) + 38 * math.log(38) + 30 * math.log(30)
def xl(w): return w * cmath.log(w)
def g(u): return sum(c * xl(b + u) for b, c in CB) + KG
def e(u): return xl(74 + u) - xl(76 + u) + 2 * math.log(2)
def g1(u): return sum(c * cmath.log(b + u) for b, c in CB)
def e1(u): return cmath.log(74 + u) - cmath.log(76 + u)
def g2(u): return sum(c / (b + u) for b, c in CB)
def e2(u): return 1 / (74 + u) - 1 / (76 + u)
def H(r, u): return (r * g(u) + e(u) - 2j * math.pi * u).real
def dF(r, u): return abs(r * g1(u) + e1(u) - 2j * math.pi)
def B2(r, u, rad):
    return r * sum(abs(c) / max(abs(b + u) - rad, 1e-9) ** 2 for b, c in CB) + sum(1 / (abs(b + u) - rad) ** 2 for b, c in EB)

def seg_cost(r, A, B, theta, cap=10**6):
    L = abs(B - A); s = 0.0; n = 0; minsl = 1e9
    while s < L and n < cap:
        u = A + (B - A) * s / L
        sl = theta - H(r, u); minsl = min(minsl, sl)
        if sl <= 0: return None, sl
        fp = dF(r, u); b2 = B2(r, u, 0.5)
        h = min(0.5, 2 * sl / (fp + 1e-12), 2 * (sl / b2) ** 0.5)
        s += max(h, 1e-7); n += 1
    return n, minsl

def plan(r, u, s0, var, s1=1.0, xR=20.0, yc=0.25, x0=-2.0, Y=200.0):
    F2 = r * g2(u) + e2(u); ph = (math.pi - cmath.phase(F2)) / 2; ee = cmath.exp(1j * ph)
    if ee.real > 0: ee = -ee
    top, bot = u + s0 * ee, u - s0 * ee
    theta = H(r, u) - abs(F2) * s0 ** 2 / 8
    if var == 'A':
        ext = u - (s0 + s1) * ee
        pcs = [(ext, bot), (top, complex(x0, 0)), (ext, complex(ext.real, -Y))]
    elif var == 'B':
        PR = complex(xR, -yc); PL = complex(top.real - 0.3, top.imag * 0.3)
        pcs = [(PR, bot), (top, PL), (PL, complex(x0, 0)), (PR, complex(xR, -Y))]
    else:  # 'C': go right horizontally from bot to xR, then down
        PR = complex(xR, bot.imag)
        pcs = [(bot, PR), (top, complex(x0, 0)), (PR, complex(xR, -Y))]
    return [seg_cost(r, A, B, theta) for A, B in pcs]

if __name__ == '__main__':
    rs = list(range(3, 50, 2))
    S = {r: complex(v) for r, v in saddle_family(rs).items()}
    for r in rs:
        best = None
        for s0 in [1.5, 1.2, 1.0, 0.8, 0.6, 0.4]:
            for var in 'ABC':
                p = plan(r, S[r], s0, var)
                if all(n is not None for n, _ in p):
                    tot = sum(n for n, _ in p)
                    if best is None or tot < best[0]:
                        best = (tot, s0, var, [(n, round(sl, 2)) for n, sl in p])
        print(r, best, flush=True)
