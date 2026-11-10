"""Compare the hybrid estimator with exhaustive enumeration, layer by layer.

usage: python -u validate_hybrid.py CODE MAX_SIZE [--samples N] [--threads T]

Prints, for every layer, the exact coefficient and the z-score of every
estimate (minimal-set, dual, stratified and plain sampling). A small MAX_SIZE
and a small sample force the stratified estimator to be used on many layers.
Also checks the duality d_E + d_{E^c} = 2k on the exact histogram, in the form
f_j 4^k = mean 2^{d_E'}. Writes results/exact_CODE.json; the hybrid result is
written to results/validation_CODE_wW_sN.json and does not overwrite a production run.
"""
import json
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

import qec_codes
import hybrid
from curves import exact_tables

if __name__ == "__main__":
    name, max_size = sys.argv[1], int(sys.argv[2])
    opt = lambda flag, default: (int(sys.argv[sys.argv.index(flag) + 1])
                                 if flag in sys.argv else default)
    samples, threads = opt("--samples", 4_000_000), opt("--threads", 8)
    code = qec_codes.get(name)
    n, k = code.n, code.k
    exact_path = Path("results") / f"exact_{name}.json"
    if exact_path.exists() and "--recount" not in sys.argv:
        data = json.loads(exact_path.read_text())
        f = [Fraction(x) for x in data["f"]]
        u = [Fraction(x) for x in data["u"]]
        b = [1 - x for x in f]
        print("exact tables read from", exact_path.name)
    else:
        f, b, u, hist = exact_tables(code)
        dual_ok = all(
            f[j] * 4 ** k == sum(Fraction(int(hist[n - j, d]) * 2 ** d, comb(n, j))
                                 for d in range(2 * k + 1)) for j in range(n + 1))
        print(f"duality f_j 4^k = mean 2^(d_E') over |E'| = n-j: {'holds' if dual_ok else 'FAILS'}")
        exact_path.write_text(json.dumps({"code": code.name, "n": n, "k": k,
                                          "f": [str(x) for x in f], "u": [str(x) for x in u]}))
    # keep the production cache and result untouched
    saved = {p: p.read_bytes() for p in (Path("results") / f"hybrid_{name}.json",
                                         Path("results") / f"minimal_{name}.json") if p.exists()}
    for p in saved:
        p.unlink()
    try:
        res = hybrid.run(name, max_size, samples=samples, threads=threads, log=lambda *a: None)
        Path("results", f"validation_{name}_w{max_size}_s{samples}.json").write_text(
            json.dumps(res, indent=1))
    finally:
        for p in (Path("results") / f"hybrid_{name}.json", Path("results") / f"minimal_{name}.json"):
            if p.exists():
                p.unlink()
        for p, content in saved.items():
            p.write_bytes(content)
    print(f"minimal sets by size {res['minimal_by_size']}, complete through {res['complete_level']}")
    worst = [0.0]

    def z(est, se, truth):
        truth = float(truth)
        if se == 0:
            ok = abs(est - truth) <= 1e-12 * max(1.0, abs(truth))
            return "exact" if ok else "WRONG"
        val = (est - truth) / se
        worst[0] = max(worst[0], abs(val))
        return f"{val:+.2f}"

    stratified = 0
    for row in res["layers"]:
        j = row["j"]
        parts = []
        if "kl" in row:
            parts.append(f"minimal: b {z(*row['kl']['b'], b[j])} u {z(*row['kl']['u'], u[j])}")
        if "kl_dual" in row:
            parts.append(f"dual: {z(*row['kl_dual']['dual'], f[j] * 4 ** k - 1)}")
        if "strat" in row:
            stratified += 1
            st = row["strat"]
            parts.append(f"stratified: b {z(*st['b'], b[j])} u {z(*st['u'], u[j])} "
                         f"(rel.se {st['b'][1] / st['b'][0]:.3f}, {st['samples']} samples, "
                         f"{st['remainder_events']} remainder events)")
        parts.append(f"sampling: f {z(*row['mc']['f'], f[j])} b {z(*row['mc']['b'], b[j])}")
        print(f"j={j:3d} b={float(b[j]):.6e} f={float(f[j]):.6e}  " + " | ".join(parts))
    print(f"largest |z| = {worst[0]:.2f}; stratified layers: {stratified}")
