"""Per-r check of (S1)-(S6) of Section 8.5 at the (numerically exact) saddle point, for a given
set of regions."""
from mpmath import mp, mpf, pi, exp, arg, sin, fabs, findroot
from family import CB, g, e, g1, e1, g2, e2, Fs, F1s, saddle_family
mp.dps = 40
EB = [(74, 1), (76, -1)]
PAPER = dict(BL=(mpf('2.092953'), mpf('2.702953'), mpf('-0.523633')),
             BR=(mpf('5.604839'), mpf(20), mpf('-0.827198')),
             rows=[(mpf('-232.243990'), mpf('-9.302985')), (mpf('-232.163207'), mpf('-9.391867')),
                   (mpf('-232.553934'), mpf('-9.194246')), (mpf('-240.067409'), mpf('-11.285922')),
                   (mpf('-238.599798'), mpf('-9.194562'))], s0=mpf('1.5'))

def check(r, u, RS=PAPER):
    F2 = r * g2(u) + e2(u)
    ph = (pi - arg(F2)) / 2
    ee = exp(1j * ph)
    if ee.real > 0: ee = -ee          # Re e^{i phi} < 0 as in 8.4
    s0 = RS['s0']
    top, bot = u + s0 * ee, u - s0 * ee
    x1, x2, yb = RS['BL']; X1, X2, Yb = RS['BR']
    S1 = (x1 <= top.real <= x2 and yb <= top.imag < 0 and X1 <= bot.real <= X2 and Yb <= bot.imag < 0)
    xi = u.real - s0
    M3 = r * sum(abs(c) / (b + xi) ** 2 for b, c in CB) + sum(abs(c) / (b + xi) ** 2 for b, c in EB)
    S2 = M3 * s0 / (mpf(3) / 2 * abs(F2))
    S3 = abs(u.imag) - s0 * abs(ee.imag)
    Hd = Fs(r, u).real
    delta = abs(F2) * s0 ** 2 / 8
    S4 = min(Hd - delta - (r * Sg + Se) for Sg, Se in RS['rows'])
    al = Fs(r, u).imag
    S5 = min(abs(al / pi - round(al / pi)), 1) * pi
    S6 = -Hd - (mpf('214.7497872') * r - 3)
    return dict(top=complex(top), bot=complex(bot), S1=S1, S2=float(S2), S3=float(S3), S4=float(S4), S5=float(S5), S6=float(S6))

if __name__ == '__main__':
    rs = list(range(3, 302, 2))
    S = saddle_family(rs)
    bad = []
    for r in rs:
        c = check(r, S[r])
        ok = c['S1'] and c['S2'] <= 1 and c['S3'] > 0 and c['S4'] > 0 and c['S5'] > 0 and c['S6'] > 0
        if not ok or r in (51, 53, 99, 101, 199, 299):
            print(r, 'OK' if ok else 'FAIL', {k: (round(v, 4) if isinstance(v, float) else v) for k, v in c.items() if k not in ('top', 'bot')}, 'top', f"{c['top']:.3f}", 'bot', f"{c['bot']:.3f}")
