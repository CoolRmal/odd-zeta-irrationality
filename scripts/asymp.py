"""The asymptotic regime of Section 8.7: all bounds as explicit functions of t = 1/r."""
from mpmath import mp, mpf, pi, sqrt, log, atan, sin, cos, fabs, findroot, factorial
from family import CB, g, e, g1, e1, g2, e2
mp.dps = 40
a = findroot(lambda x: g1(x), mpf('4.19'))
D = -g2(a)
g3 = sum(c * 2 / (b + a) ** 3 for b, c in CB)          # g'''(a) = sum c * 2/(b+a)^3 ... sign: d/du c/(b+u) = -c/(b+u)^2
g3 = sum(-c / (b + a) ** 2 for b, c in CB)
EB = [(74, 1), (76, -1)]
E1a = e1(a); E2a = e2(a)
ga = g(a); ea = e(a)
nu = sqrt(4 * pi ** 2 + E1a ** 2) / D

def M(k, tau):
    return factorial(k - 2) * sum(abs(c) / (b + a - tau) ** (k - 1) for b, c in CB)

def E(k, tau):
    if k == 1:
        return abs(E1a) + E(2, tau) * tau
    return factorial(k - 2) * sum(abs(c) / (b + a - tau) ** (k - 1) for b, c in EB)

def bounds(R):
    t = mpf(1) / R; r = mpf(R)
    tau1 = nu * t
    N1 = M(3, tau1) * nu ** 2 / 2 + E(2, tau1) * nu
    N2 = r * D - M(3, tau1) * nu - E(2, tau1)
    etab = N1 / (r * N2)
    L = r * M(3, tau1 + 2 * etab) + E(3, tau1 + 2 * etab)
    h = L * etab / N2
    eps = 2 * etab
    tau = tau1 + eps
    kappa2 = g3 * (E1a - 2j * pi) / D
    Th2 = r * M(4, tau) * tau ** 2 / 2 + r * abs(g3) * eps + E(2, tau)
    F2m = r * D - abs(kappa2.real) - Th2
    F2p = r * D + abs(kappa2) + Th2
    T = (abs(kappa2.imag) + Th2) / F2m
    sinphi = sin(atan(T) / 2); cosphi = cos(atan(T) / 2)
    Dp = r * M(2, tau) * tau ** 2 / 2 + E(1, tau) * tau
    Dm = Dp + 2 * pi * (2 * pi / (r * D) + eps)
    alpha2 = g3 * (8 * pi ** 3 - 6 * pi * E1a ** 2) / (6 * D ** 3)
    Da = D * eps * (2 * nu + r * eps) / 2 + r * abs(g3) * eps * tau ** 2 / 2 + r * M(4, tau) * tau ** 4 / 24 + E(2, tau) * tau ** 2 / 2 + abs(E1a) * eps + 2 * pi * eps
    s0 = mpf('1.5')
    imu_lo, imu_hi = 2 * pi / (r * D) - eps, 2 * pi / (r * D) + eps       # |Im u*|
    reu_lo, reu_hi = a + E1a / (r * D) - eps, a + E1a / (r * D) + eps
    # (S1) top in B_L=[2.092953,2.702953]x[-0.523633,0], bot in B_R=[5.604839,20]x[-0.827198,0]
    top_re = (reu_lo - s0, reu_hi - s0 * cosphi)
    top_im = (-imu_hi - s0 * sinphi, -imu_lo + s0 * sinphi)
    bot_re = (reu_lo + s0 * cosphi, reu_hi + s0)
    S1 = top_re[0] >= mpf('2.092953') and top_re[1] <= mpf('2.702953') and top_im[0] >= mpf('-0.523633') and top_im[1] < 0 \
        and bot_re[0] >= mpf('5.604839') and bot_re[1] <= 20 and top_im[0] >= mpf('-0.827198')
    # (S2) M3^sigma s0 <= 3/2 |F''| with xi = Re u* - s0
    xi = reu_lo - s0
    M3hp = factorial(1) * sum(abs(c) / (b + xi) ** 2 for b, c in CB)
    E3hp = sum(abs(c) / (b + xi) ** 2 for b, c in EB)
    S2 = (r * M3hp + E3hp) * s0 / (mpf(3) / 2 * F2m)
    # (S3) y_sigma = |Im u*| - s0 |sin phi| > 0
    S3 = imu_lo - s0 * sinphi
    # (S4) r Gamma >= Delta^- + (F2p - rD) s0^2/8 + S_e - e(a); rows (Gamma, S_e)
    rows = [(mpf('0.146966'), mpf('-9.302985')), (mpf('0.066184'), mpf('-9.391867')), (mpf('0.456911'), mpf('-9.194246')),
            (mpf('7.970386'), mpf('-11.285922')), (mpf('6.502774'), mpf('-9.194562'))]
    S4 = min(r * G - (Dm + (F2p - r * D) * s0 ** 2 / 8 + Se - ea) for G, Se in rows)
    # (S5) dist(alpha, pi Z) >= pi dist(2a, Z) - 2 pi |e1|/(rD) - |alpha2|/r^2 - Da
    d2a = min(abs(2 * a - round(2 * a)), 1)
    S5 = pi * d2a - 2 * pi * abs(E1a) / (r * D) - abs(alpha2) / r ** 2 - Da
    # (S6) -H_d - (c2bar r - 3) >= -r ghat(a) - e(a) - Dp - (214.6595862475 r - 3)
    S6 = -r * ga - ea - Dp - (mpf('214.6595862475') * r - 3)
    return dict(h=float(h), S1=S1, S2=float(S2), S3=float(S3), S4=float(S4), S5=float(S5), S6=float(S6))

if __name__ == '__main__':
    print('a', a, 'D', D, 'g3', g3, 'nu', nu)
    for R in [20001, 10001, 5001, 2001, 1001, 501, 301, 201, 101, 51]:
        print(R, bounds(R))
