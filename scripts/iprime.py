"""Rational lower bound I' for I_Phi: truncate the sum over periods at K."""
from fractions import Fraction as Fr
from phi import CASES, mhat, phi, breakpoints
import pickle, sys

def phi_table(name):
    c = CASES[name]
    X = breakpoints(c)
    vals = [phi(c, (X[i] + X[i + 1]) / 2) for i in range(len(X) - 1)]
    return X, vals

def iprime(name, K, X, vals):
    c = CASES[name]; m0, m = mhat(c)
    I = 0.0
    lo = Fr(1, m0)
    for i in range(len(X) - 1):
        a, b, v = X[i], X[i + 1], vals[i]
        if v == 0: continue
        s = sum(1.0 / (k + float(a)) - 1.0 / (k + float(b)) for k in range(1, K + 1))
        if a >= lo:
            s += 1.0 / float(a) - 1.0 / float(b)
        I += v * s
    return I

if __name__ == '__main__':
    for name in 'AB':
        X, vals = phi_table(name)
        pickle.dump((X, vals), open(f'phi_{name}.pkl', 'wb'))
        c = CASES[name]; m0, m = mhat(c)
        ms = c['r'] * m[0] + sum(m[1:])
        print(name, 'intervals', len(vals), 'nonzero', sum(1 for v in vals if v), 'avg phi', sum(float(X[i+1]-X[i])*vals[i] for i in range(len(vals))))
        for K in [5, 10, 20, 40, 80, 160]:
            I = iprime(name, K, X, vals)
            print('  K', K, "I'", round(I, 4), "C2'", round(ms - I, 4))
