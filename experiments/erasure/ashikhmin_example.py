"""External check against a published table: Example 1 of A. Ashikhmin, "Fidelity of Finite
Length Quantum Codes in Qubit Erasure Channel", ISIT 2020, doi 10.1109/ISIT44484.2020.9174340.

usage: python -u ashikhmin_example.py

That example lists, for a [[12,6]] F_4-linear code, the nonzero invariants

    N_i^{r,rbar} = #{E : |E| = i, dim_{F_4} S_E = r, dim_{F_4} N_E = rbar}

(S_E, N_E: stabilizer and normalizer elements supported on E) and the numbers U_i of
unrecoverable sets of size i. In the notation of the paper d_E = 2 (rbar - r), so

    U_i = sum_{rbar > r} N_i^{r,rbar},     sum_{|E| = i} 2^{-d_E} = sum_{r,rbar} N_i^{r,rbar} 4^{r - rbar}.

This script

  1. recomputes all N_i^{r,rbar} by a standalone enumeration (its own GF(2) elimination,
     nothing shared with gf2.py) and compares them with the published list;
  2. computes the tables f_j, u_j with the pipeline's enumerator (curves.exact_tables),
     checks them against the values implied by the published invariants, and writes
     results/exact_ashikhmin12.json, the reference that `exact_lean.py ashikhmin12`
     compares the verified Lean table with;
  3. writes results/ashikhmin_example.json.
"""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path

import qec_codes
from curves import exact_tables

HERE = Path(__file__).resolve().parent
N_QUBITS = 12

# Nonzero values printed in Example 1, keyed (i, r, rbar).
PUBLISHED = {(0, 0, 0): 1, (1, 0, 0): 12, (2, 0, 0): 66, (3, 0, 0): 184, (3, 0, 1): 36,
             (4, 0, 1): 486, (4, 0, 2): 9, (5, 0, 2): 792, (6, 0, 3): 924, (7, 0, 4): 792,
             (8, 0, 5): 486, (8, 1, 5): 9, (9, 0, 6): 184, (9, 1, 6): 36, (10, 1, 7): 66,
             (11, 2, 8): 12, (12, 3, 9): 1}
# "U_1 = 0, U_2 = 0, U_3 = 36, and U_j = C(12, j), j >= 4."
PUBLISHED_U = [0, 0, 0, 36] + [comb(N_QUBITS, j) for j in range(4, N_QUBITS + 1)]


def rank(vectors):
    basis = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def kernel(equations, width):
    """Basis of {x : parity(x & e) = 0 for every e in equations}."""
    pivots = {}
    for e in equations:
        for p, b in pivots.items():
            if e >> p & 1:
                e ^= b
        if e:
            p = e.bit_length() - 1
            for q in list(pivots):
                if pivots[q] >> p & 1:
                    pivots[q] ^= e
            pivots[p] = e
    out = []
    for free in range(width):
        if free in pivots:
            continue
        x = 1 << free
        for p, b in pivots.items():
            if b >> free & 1:
                x |= 1 << p
        out.append(x)
    return out


def invariants(code):
    n = code.n
    low = (1 << n) - 1
    stab = [sum(int(x) << i for i, x in enumerate(row)) for row in code.h]  # x bits low, z bits high
    swap = lambda v: (v >> n) | ((v & low) << n)
    norm = kernel([swap(s) for s in stab], 2 * n)
    stab_basis = [s for i, s in enumerate(stab) if rank(stab[:i + 1]) > rank(stab[:i])]
    assert len(norm) + len(stab_basis) == 2 * n

    def supported_dim(basis, erased):
        mask = sum((1 << i) | (1 << (n + i)) for i in range(n) if i not in erased)
        return len(basis) - rank([b & mask for b in basis])

    table = Counter()
    for size in range(n + 1):
        for erased in combinations(range(n), size):
            erased = set(erased)
            ds, dn = supported_dim(stab_basis, erased), supported_dim(norm, erased)
            assert ds % 2 == 0 and dn % 2 == 0  # F_4-linear
            table[(size, ds // 2, dn // 2)] += 1
    return dict(table)


def main():
    code = qec_codes.get("ashikhmin12")
    n = code.n
    assert (n, code.k) == (N_QUBITS, 6)
    table = invariants(code)
    same = table == PUBLISHED
    print(f"{code.name}: {len(table)} nonzero invariants; identical to the published list: {same}")
    for key in sorted(set(table) | set(PUBLISHED)):
        if table.get(key) != PUBLISHED.get(key):
            print("  differs at", key, "computed", table.get(key), "published", PUBLISHED.get(key))

    f, _, u, _ = exact_tables(code)
    f_published = [sum(Fraction(c, 4 ** (rb - r)) for (i, r, rb), c in PUBLISHED.items() if i == j) / comb(n, j)
                   for j in range(n + 1)]
    u_published = [Fraction(PUBLISHED_U[j], comb(n, j)) for j in range(n + 1)]
    f_ok, u_ok = f == f_published, u == u_published
    print("pipeline table f_j equals the layer averages implied by the published invariants:", f_ok)
    print("pipeline table u_j equals the published U_j / C(12, j):", u_ok)
    (HERE / "results" / "exact_ashikhmin12.json").write_text(json.dumps(
        {"code": code.name, "n": n, "k": code.k, "f": [str(x) for x in f], "u": [str(x) for x in u]}))
    (HERE / "results" / "ashikhmin_example.json").write_text(json.dumps({
        "source": "Ashikhmin, ISIT 2020, doi 10.1109/ISIT44484.2020.9174340, Example 1",
        "code": code.name,
        "invariants": {f"{i},{r},{rb}": c for (i, r, rb), c in sorted(table.items())},
        "invariants_match_published": same,
        "U": [int(u[j] * comb(n, j)) for j in range(n + 1)],
        "u_matches_published": u_ok,
        "f": [str(x) for x in f],
        "f_matches_published_invariants": f_ok}, indent=1) + "\n")
    raise SystemExit(0 if same and f_ok and u_ok else 1)


if __name__ == "__main__":
    main()
