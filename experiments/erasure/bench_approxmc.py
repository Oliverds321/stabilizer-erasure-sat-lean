"""Timing probe: how far does off-the-shelf ApproxMC get on the certificate CNFs?

usage: python -u bench_approxmc.py CODE EPS j1 j2 ... [--full]
"""
import sys
import time
from math import comb, log2

import qec_codes
from certificates import layer_formula, approx_count

args = [a for a in sys.argv[1:] if not a.startswith("--")]
code = qec_codes.get(args[0])
eps = float(args[1])
reduced = "--full" not in sys.argv
print(f"{code.name}: n={code.n} k={code.k} nnz={code.nnz} reduced={reduced} eps={eps}", flush=True)
for j in map(int, args[2:]):
    for kind in ("good", "bad"):
        f, proj = layer_formula(code, j, kind, reduced=reduced)
        t = time.time()
        est = approx_count(f, proj, eps, 0.1)
        dt = time.time() - t
        total = comb(code.n, j) * (4 ** code.k if reduced else 2 ** (2 * code.n - code.s))
        lg = log2(est) if est else float("-inf")
        print(f"  j={j:3d} {kind:4s} vars={f.nvars:6d} clauses={len(f.clauses):6d} width={f.width} "
              f"proj={len(proj):4d} log2(est)={lg:8.2f} fraction={est / total:.4g} "
              f"time={dt:7.1f}s", flush=True)
