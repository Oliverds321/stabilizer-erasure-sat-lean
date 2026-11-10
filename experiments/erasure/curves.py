"""Coefficient tables and curves.

f_j  : Bernstein coefficient of the fidelity curve, the mean of 2^{-d_E} over |E| = j.
b_j  : 1 - f_j, the infidelity coefficient.
u_j  : fraction of uncorrectable sets of size j.

F(p) = sum_j f_j C(n,j) p^j (1-p)^(n-j),  I(p) = 1 - F(p),  U(p) likewise from u_j.
"""
from fractions import Fraction
from math import comb, lgamma, log, exp

from gf2 import enumerate_all


def exact_tables(code, threads=8):
    """Exact f_j, b_j, u_j as Fractions, from the full (|E|, d_E) histogram."""
    hist = enumerate_all(code, threads=threads)
    n, k = code.n, code.k
    f, u = [], []
    for j in range(n + 1):
        total = comb(n, j)
        assert int(hist[j].sum()) == total
        f.append(sum(Fraction(int(hist[j, d]), 2 ** d) for d in range(2 * k + 1)) / total)
        u.append(Fraction(sum(int(hist[j, d]) for d in range(1, 2 * k + 1)), total))
    return f, [1 - x for x in f], u, hist


def log_weight(n, j, p):
    """log of C(n,j) p^j (1-p)^(n-j) for 0 < p < 1."""
    return (lgamma(n + 1) - lgamma(j + 1) - lgamma(n - j + 1)
            + j * log(p) + (n - j) * log(1 - p))


def bernstein(coeffs, p):
    """sum_j coeffs[j] C(n,j) p^j (1-p)^(n-j), stable for very small p."""
    n = len(coeffs) - 1
    if p <= 0:
        return float(coeffs[0])
    if p >= 1:
        return float(coeffs[n])
    return sum(float(c) * exp(log_weight(n, j, p)) for j, c in enumerate(coeffs) if c)


def repair(g, first, last):
    """Anchored antitone repair (Lemma "Anchored antitone repair") on a chain.

    g: raw estimates of an antitone table; first/last: exact anchor values.
    """
    n = len(g) - 1
    bar = [min(1.0, max(0.0, float(x))) for x in g]
    bar[0], bar[n] = float(first), float(last)
    out, running = [], 1.0
    for j in range(n + 1):
        running = min(running, bar[j])
        out.append(max(float(last), running))
    return out


def two_tail_error(est_f, true_f, p):
    """(relative fidelity error, relative infidelity error) at p."""
    fe, ft = bernstein(est_f, p), bernstein(true_f, p)
    ie = bernstein([1 - x for x in est_f], p)
    it = bernstein([1 - x for x in true_f], p)
    return abs(fe - ft) / ft, (abs(ie - it) / it if it > 0 else (0.0 if ie == 0 else float("inf")))
