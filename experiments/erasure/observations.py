"""Print the numbers quoted in the prose of the paper's computed section
(leading coefficients, ratios to the leading term, split-layer statistics).

usage: python observations.py
"""
import json
from math import comb

import numpy as np
from analyze import hybrid_runs, hybrid_rows
from curves import bernstein

hyb = hybrid_runs()
rows = {r["key"]: r for r in hybrid_rows(hyb)}
ps = np.logspace(-4, -0.0005, 600)
for key, (r, est) in hyb.items():
    n, k, d, w = r["n"], r["k"], r["distance"], r["complete_level"]
    b = [1 - x for x in est["f_hat"]]
    lead = b[d] * comb(n, d)
    ratio = [bernstein(b, p) / (lead * p ** d) for p in ps]
    i = int(np.argmax(ratio))
    j = int(np.argmin(ratio))
    at = {p: bernstein(b, p) / (lead * p ** d) for p in (0.01, 0.02, 0.05, 0.1, 0.2, 0.3)}
    src = est["source"]
    counts = {s: src.count(s) for s in sorted(set(src))}
    worst_b = max(range(d, n + 1), key=lambda t: est["rel_b"][t])
    worst_f = max(range(n + 1), key=lambda t: est["rel_f"][t])
    strat = [(row["j"], row["strat"]["samples"], row["strat"]["remainder_events"],
              round(row["strat"]["b"][1] / row["strat"]["b"][0], 4)) for row in r["layers"]
             if "strat" in row]
    smallest_mc = min(((est["b"][t], t) for t in range(n + 1) if src[t] == "sampling"),
                      default=None)
    print(f"== {r['code']} n={n} k={k} d={d} w={w} sat={r['sat_seconds']:.0f}s "
          f"wall={r['wall_seconds']:.0f}s threads={r.get('threads')}")
    print(f"   minimal {r['minimal_by_size']}")
    print(f"   leading coefficient c = C(n,d)(1-f_d) = {lead:.6g};  1-f_d = {b[d]:.4g}")
    print("   ratio to leading term: " + ", ".join(f"p={p}: {v:.3f}" for p, v in at.items()))
    print(f"   max ratio {ratio[i]:.3f} at p={ps[i]:.3f}; min ratio {ratio[j]:.3f} at p={ps[j]:.3f}")
    print(f"   sources {counts}")
    print(f"   worst rel se: b {est['rel_b'][worst_b]:.4f} at j={worst_b} ({src[worst_b]}), "
          f"f {est['rel_f'][worst_f]:.4f} at j={worst_f} ({src[worst_f]})")
    print(f"   stratified layers (j, samples, remainder events, rel se): {strat}")
    print(f"   smallest plainly sampled 1-f_j: {smallest_mc}")
    print(f"   total plain samples {sum(row['mc']['samples'] for row in r['layers']):.3g}")
    lead_row = r["layers"][d]["kl"]
    print(f"   leading layer exact={lead_row.get('exact')} classes={lead_row.get('by_exponent')}")
    shares = [(rw["j"], round(rw["strat"]["remainder"]["b"][0] / rw["strat"]["b"][0], 4))
              for rw in r["layers"] if "strat" in rw]
    print(f"   remainder share of b by stratified layer: {shares}")
    row = rows[key]
    print(f"   I at {row['I_at']}  p_half {row['p_half']}")
    if "max_inf_err" in row:
        print(f"   vs exact: errI {row['max_inf_err']:.3g} errF {row['max_fid_err']:.3g} "
              f"coef b {row['coef_b_err']:.3g} coef f {row['coef_f_err']:.3g}")

total = zero = 0
bound = share = 0.0
for key, (r, est) in hyb.items():
    for rw in r["layers"]:
        if "strat" in rw:
            st = rw["strat"]
            total += 1
            share = max(share, st["remainder"]["b"][0] / st["b"][0])
            if st["remainder_events"] == 0:
                zero += 1
                bound = max(bound, 3.0 / st["samples"] / st["b"][0])
print(f"split layers: {total}, without remainder event: {zero}, "
      f"largest 3/M bound relative to the layer sum: {100 * bound:.2f}%, "
      f"largest remainder share: {100 * share:.2f}%")
