"""Validate the encodings on small codes against exhaustive enumeration.

For every layer j of every small code:
  * exact A_j, B_j from the (|E|, d_E) histogram;
  * the number of projected models of the Good / Bad 3-CNF, by blocking-clause
    enumeration, in the paper's (E, z) projection and in the reduced (E, a) one;
  * the number of uncorrectable sets from the E-only projection.
All must agree exactly.
"""
import sys
import time
from math import comb

import qec_codes
from certificates import layer_formula, uncorrectable_formula, enumerate_projected
from gf2 import enumerate_all


def check_sets_only(name):
    """Larger codes: only the E-projection (uncorrectable sets) is enumerable."""
    code = qec_codes.get(name)
    n, k = code.n, code.k
    hist = enumerate_all(code, threads=4)
    ok = True
    for j in range(n + 1):
        unc = sum(int(hist[j, d]) for d in range(1, 2 * k + 1))
        f, proj = uncorrectable_formula(code, j)
        got = len(enumerate_projected(f, proj)[0])
        if got != unc:
            ok = False
            print(f"  MISMATCH {name} j={j}: exact {unc} cnf {got}", flush=True)
    print(f"{code.name:28s} layers 0..{n}: "
          f"{'uncorrectable-set counts agree' if ok else 'FAILED'}", flush=True)
    return ok


def check(name, full_projection=True):
    code = qec_codes.get(name)
    n, k, s = code.n, code.k, code.s
    hist = enumerate_all(code, threads=4)
    z_card = 2 ** (2 * n - s)
    ok = True
    widths = set()
    for j in range(n + 1):
        # 2^{2k} * sum_E 2^{-d_E}: integer because d_E <= 2k
        good_red = sum(int(hist[j, d]) * 4 ** k // 2 ** d for d in range(2 * k + 1))
        bad_red = comb(n, j) * 4 ** k - good_red
        unc = sum(int(hist[j, d]) for d in range(1, 2 * k + 1))
        scale = z_card // 4 ** k
        f, proj = layer_formula(code, j, "good", reduced=True)
        widths.add(f.width)
        got_g = len(enumerate_projected(f, proj)[0])
        f, proj = layer_formula(code, j, "bad", reduced=True)
        got_b = len(enumerate_projected(f, proj)[0])
        f, proj = uncorrectable_formula(code, j)
        got_u = len(enumerate_projected(f, proj)[0])
        line_ok = (got_g, got_b, got_u) == (good_red, bad_red, unc)
        if full_projection:
            f, proj = layer_formula(code, j, "good", reduced=False)
            widths.add(f.width)
            full_g = len(enumerate_projected(f, proj)[0])
            f, proj = layer_formula(code, j, "bad", reduced=False)
            full_b = len(enumerate_projected(f, proj)[0])
            line_ok &= (full_g, full_b) == (good_red * scale, bad_red * scale)
        ok &= line_ok
        if not line_ok:
            print(f"  MISMATCH {name} j={j}: exact {(good_red, bad_red, unc)} "
                  f"cnf {(got_g, got_b, got_u)}")
    print(f"{code.name:28s} layers 0..{n}: {'all counts agree' if ok else 'FAILED'}; "
          f"max clause width {max(widths)}")
    return ok


if __name__ == "__main__":
    start = time.time()
    results = [check("five"), check("steane"), check("shor9", full_projection=False),
               check("surface3", full_projection=False), check_sets_only("hamming15")]
    print(f"{'PASS' if all(results) else 'FAIL'} in {time.time() - start:.0f}s")
    sys.exit(0 if all(results) else 1)
