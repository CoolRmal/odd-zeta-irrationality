import cmath, math
from small_r_fast import H, dF, g2, e2, CB, EB, saddle_family
def B2loc(r, u, h):
    # bound for |F''| on the disc of radius h around u
    return r * sum(1 / max(abs(b + u) - h, 1e-12) ** 2 for b, c in CB) + sum(1 / (abs(b + u) - h) ** 2 for b, c in EB)
def seg_cost(r, A, B, theta, hmax):
    L = abs(B - A); s = 0.0; n = 0; minsl = 1e9
    while s < L:
        u = A + (B - A) * s / L
        sl = theta - H(r, u); minsl = min(minsl, sl)
        if sl <= 0: return None, sl
        fp = dF(r, u); h = hmax
        while h > 1e-9 and (h / 2) * (fp + (h / 2) * B2loc(r, u, h)) > sl: h /= 1.5
        s += h; n += 1
        if n > 200000: return None, -1
    return n, minsl
def plan(r, u, s0, xR=20.0, x0=-2.0, Y=170.0):
    F2 = r * g2(u) + e2(u); ph = (math.pi - cmath.phase(F2)) / 2; ee = cmath.exp(1j * ph)
    if ee.real > 0: ee = -ee
    top, bot = u + s0 * ee, u - s0 * ee
    theta = H(r, u) - abs(F2) * s0 ** 2 / 8
    PR = complex(xR, bot.imag)
    return [seg_cost(r, bot, PR, theta, 1.0), seg_cost(r, top, complex(x0, 0), theta, 1.0), seg_cost(r, PR, complex(xR, -Y), theta, 20.0)]
if __name__ == "__main__":
    rs = list(range(3, 50, 2))
    S = {r: complex(v) for r, v in saddle_family(rs).items()}
    tot_all = 0
    for r in rs:
        best = None
        for s0 in [1.5, 1.2, 1.0, 0.8]:
            p = plan(r, S[r], s0)
            if all(n is not None for n, _ in p):
                tot = sum(n for n, _ in p)
                if best is None or tot < best[0]: best = (tot, s0, [(n, round(sl, 2)) for n, sl in p])
        tot_all += best[0] if best else 0
        print(r, best, flush=True)
    print('total grid points', tot_all)
