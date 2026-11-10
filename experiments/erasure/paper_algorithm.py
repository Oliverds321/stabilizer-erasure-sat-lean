"""The algorithm of the main theorem, run with off-the-shelf components.

For every layer j the two projected counts A_j (Good) and B_j (Bad) of the
3-CNF certificates are estimated by ApproxMC, a hashing-based approximate
model counter that uses only a SAT solver, with tolerance eta = eps/3 and
failure probability delta / (2(n+1)). Then

    g_j = A_j / (A_j + B_j),   repaired with exact endpoints 1 and 4^{-k}.

Differences from the theorem: ApproxMC hashes with dense random XOR
constraints instead of the linear-size hash, CryptoMiniSat replaces the
subexponential engine, and (by default) z is projected through a logical basis
(`reduced=True`), which shortens the projection from 3n to n + 2k bits.

usage: python -u paper_algorithm.py CODE EPS [--full] [--workers W] [--delta D]
writes results/paper_CODE_epsEPS.json
"""
import json
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import qec_codes
from certificates import layer_formula, approx_count, satisfiable
from curves import repair

HERE = Path(__file__).resolve().parent


def count_layer(task):
    name, j, kind, reduced, eta, zeta, seed = task
    code = qec_codes.get(name)
    f, proj = layer_formula(code, j, kind, reduced=reduced)
    start = time.time()
    if not satisfiable(f):  # the deterministic zero test
        return j, kind, 0, time.time() - start, f.nvars, len(f.clauses)
    est = approx_count(f, proj, eta, zeta, seed=seed)
    return j, kind, est, time.time() - start, f.nvars, len(f.clauses)


def run(name, eps, delta=0.1, reduced=True, workers=6, seed=1):
    code = qec_codes.get(name)
    n, k = code.n, code.k
    eta, zeta = eps / 3, delta / (2 * (n + 1))
    tasks = [(name, j, kind, reduced, eta, zeta, seed + 2 * j + (kind == "bad"))
             for j in range(n + 1) for kind in ("good", "bad")]
    good, bad, seconds = [0] * (n + 1), [0] * (n + 1), [0.0] * (n + 1)
    size = {}
    start = time.time()
    tag = "full" if not reduced else "reduced"
    (HERE / "results").mkdir(exist_ok=True)
    cache_path = HERE / "results" / f"cache_paper_{name}_eps{eps}_{tag}.json"
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}

    def record(j, kind, est, dt, nv, nc):
        (good if kind == "good" else bad)[j] = est
        seconds[j] += dt
        size[kind] = max(size.get(kind, (0, 0)), (nv, nc))

    for key, (est, dt, nv, nc) in cache.items():  # counts finished by an earlier run
        j, kind = key.split(":")
        record(int(j), kind, int(est), dt, nv, nc)
    todo = [t for t in tasks if f"{t[1]}:{t[2]}" not in cache]
    print(f"{name}: {len(tasks) - len(todo)} counts cached, {len(todo)} to run", flush=True)
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(count_layer, t) for t in todo]):
            j, kind, est, dt, nv, nc = fut.result()
            record(j, kind, est, dt, nv, nc)
            cache[f"{j}:{kind}"] = (str(est), dt, nv, nc)
            cache_path.write_text(json.dumps(cache))
            print(f"  {name} j={j:3d} {kind:4s} est={est} ({dt:.1f}s)", flush=True)
    g = [good[j] / (good[j] + bad[j]) for j in range(n + 1)]
    f_hat = repair(g, 1.0, 4.0 ** (-k))
    out = {"code": code.name, "key": name, "n": n, "k": k, "nnz": code.nnz, "eps": eps,
           "delta": delta, "eta": eta, "zeta": zeta, "reduced": reduced,
           "good": [str(x) for x in good], "bad": [str(x) for x in bad],
           "raw": g, "f_hat": f_hat, "layer_seconds": seconds,
           "formula_size": size, "wall_seconds": time.time() - start, "workers": workers}
    path = HERE / "results" / f"paper_{name}_eps{eps}_{tag}.json"
    path.write_text(json.dumps(out, indent=1))
    print(f"wrote {path.name}: wall {out['wall_seconds']:.0f}s", flush=True)
    return out


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = lambda flag, default: (type(default)(sys.argv[sys.argv.index(flag) + 1])
                                 if flag in sys.argv else default)
    run(args[0], float(args[1]), delta=opt("--delta", 0.1), reduced="--full" not in sys.argv,
        workers=opt("--workers", 6))
