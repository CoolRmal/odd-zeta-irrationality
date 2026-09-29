"""Per-r path design for 3 <= r <= 299: -i inf -> P_R = 20 - i/4 -> bot -> sigma -> top -> P_L -> -2."""
import cmath, math, sys
from small_r_fast2 import seg_cost, H, dF, g2, e2
from family import saddle_family
def plan(r, u, s0=1.5):
    F2 = r * g2(u) + e2(u); ph = (math.pi - cmath.phase(F2)) / 2; ee = cmath.exp(1j * ph)
    if ee.real > 0: ee = -ee
    top, bot = u + s0 * ee, u - s0 * ee
    theta = H(r, u) - abs(F2) * s0 ** 2 / 8
    PR = complex(20, -0.25); PL = (top + complex(-2, 0)) / 2
    ray_bound = r * (-240.0670) - 9.7210 - 2 * math.pi * 0.25        # regRay_bound at the top of the ray
    return [seg_cost(r, PR, bot, theta, 1.0), seg_cost(r, top, PL, theta, 1.0), seg_cost(r, PL, complex(-2, 0), theta, 1.0)], theta - ray_bound, top, bot
if __name__ == '__main__':
    rs = list(range(3, 300, 2))
    S = {r: complex(v) for r, v in saddle_family(rs).items()}
    tot = 0
    for r in rs:
        p, rayslack, top, bot = plan(r, S[r])
        ok = all(n is not None for n, _ in p) and rayslack > 0 and top.imag < 0 and bot.imag < 0
        tot += sum(n for n, _ in p if n)
        if not ok or r in (3, 5, 9, 25, 49, 51, 101, 201, 299):
            print(r, 'OK' if ok else 'FAIL', [(n, round(sl, 2)) for n, sl in p], 'ray slack', round(rayslack, 1), 'top', f'{top:.3f}', 'bot', f'{bot:.3f}', flush=True)
    print('total grid points', tot)
