"""Proof-checked completeness of the lists of minimal uncorrectable sets.

usage: python -u certify.py CODE [--from L] [--to L] [--timeout S] [--symmetric]
                                 [--max-proof-mb MB] [--split-depth K] [--lean]

For a level L the instance is

    (there is an uncorrectable erased set E)  and  |E| <= L
    and  E contains none of the listed sets of size <= L.

It is written as DIMACS, refuted by CaDiCaL with an LRAT proof, and the proof
is checked by Lean's verified LRAT checker (tools/lrat/CheckLrat.lean, which
runs Std.Tactic.BVDecide.LRAT.check; soundness is the core theorem
check_sound). A verified level L therefore certifies, for the formula in the
file: every uncorrectable set of size <= L contains a listed set. Together
with the two checks made here by Gaussian elimination (every listed set is
uncorrectable; none is smaller than the claimed distance d) this gives

    distance = d,
    the uncorrectable sets of size d are exactly the listed sets of size d
        (so the leading coefficient is the finite sum over them),
    the union identity used for the layers j <= L.

Levels are tried in increasing order, each with a time limit; a level implies
all lower ones. If a refutation is too large to check in memory, or the solver
runs out of time, the instance is split on one more "qubit erased / not
erased" variable and both halves are refuted and checked separately (the
leaves of such a binary case split cover every assignment, so the instance is
unsatisfiable when every leaf is). With --symmetric one instance per orbit representative q is
refuted, with the extra unit clause "q is erased"; this is enough because the
list is closed under the (verified) symmetry group and every minimal
uncorrectable set has a translate through a representative
(lean/HybridSymmetry.lean, minimal_eq_image_through_representative).

Not covered by the proof check in the default mode: that the CNF produced by
`_logical_formula` expresses uncorrectability (tested against exhaustive
enumeration on small codes by test_small.py and validate_hybrid.py).

With --lean the formula is not written by Python at all. An instance file
(check rows, level, listed sets, unit constraints) is passed to the Lean
program tools/lrat/CertifyList.lean, which builds the formula `certFormula`
of lean/CompletenessFormula.lean, writes its DIMACS form for CaDiCaL, and
afterwards checks the LRAT proof against the formula it built itself. The
meaning of a successful check is then a Lean theorem (`certFormula_checked`):
every uncorrectable set of size <= L that satisfies the unit constraints
contains a listed set. Results go to results/certified_lean_CODE.json. The
Lean-defined formula is larger (explicit z in the normalizer, sequential
counter), so its refutations are several times longer.

The DIMACS files and proofs go to ../../../certify_work (outside the
repository; proofs can be large); results/certified_CODE.json keeps sizes,
times and SHA-256 hashes of the formulas.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

import psutil

import qec_codes
from gf2 import exponent_of
from hybrid import HERE, _logical_formula, _orbit_representatives, symmetry_group

REPO = HERE.parent.parent
LEAN_BIN = REPO.parent / "local-build" / "lean-4.34.1-windows" / "bin"
CHECKER = REPO / "tools" / "lrat" / "CheckLrat.lean"
WORK = REPO.parent / "certify_work"


def instance(code, mins, level, rep=None):
    """Clauses and variable count of the level instance (unit clause e[rep] if given)."""
    from pysat.card import CardEnc, EncType
    f, e = _logical_formula(code)
    enc = CardEnc.atmost(lits=e, bound=level, top_id=f.nvars, encoding=EncType.totalizer)
    clauses = [list(c) for c in f.clauses] + [list(c) for c in enc.clauses]
    if rep is not None:
        clauses.append([e[rep]])
    clauses += [[-e[i] for i in m] for m in mins if len(m) <= level]
    nvars = max(max(abs(x) for x in c) for c in clauses)
    return clauses, nvars


def write_dimacs(path, clauses, nvars):
    with open(path, "w", newline="\n") as out:
        out.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            out.write(" ".join(map(str, c)) + " 0\n")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_order(code, q):
    """Qubits other than q, those sharing most checks with q first."""
    import numpy as np
    h = np.array(code.h, dtype=np.uint8) % 2
    n = code.n
    touch = (h[:, :n] | h[:, n:]).astype(np.int64)
    if q is None:
        score = touch.sum(axis=0)
    else:
        score = touch.T @ touch[:, q]
    return [i for i in sorted(range(n), key=lambda i: (-int(score[i]), i)) if i != q]


def refute_split(stem, clauses, nvars, e, order, cube, timeout, max_proof_mb, max_depth, leaves):
    """Refute clauses + cube, splitting further when the proof cannot be checked."""
    cnf = WORK / (stem + "".join("p" if x > 0 else "n" for x in cube) + ".cnf")
    sha = write_dimacs(cnf, clauses + [[x] for x in cube], nvars)
    res = refute_and_check(cnf, timeout, max_proof_mb)
    cnf.unlink(missing_ok=True)
    res.update({"cube": [(order[i] if x > 0 else -order[i] - 1) for i, x in enumerate(cube)],
                "cnf_sha256": sha})
    if res["status"] == "verified":
        leaves.append(res)
        print(f"      leaf depth {len(cube)}: verified (solve {res['solve_seconds']:.0f}s, "
              f"proof {res['proof_bytes'] / 2 ** 20:.0f} MiB, check {res['check_seconds']:.0f}s)",
              flush=True)
        return True
    retry = res["status"].startswith(("refuted, proof", "solver timeout", "CHECK ABORTED"))
    if not retry or len(cube) >= max_depth:
        leaves.append(res)
        print(f"      leaf depth {len(cube)}: {res['status']}", flush=True)
        return False
    v = e[order[len(cube)]]
    return (refute_split(stem, clauses, nvars, e, order, cube + [v], timeout, max_proof_mb,
                         max_depth, leaves)
            and refute_split(stem, clauses, nvars, e, order, cube + [-v], timeout, max_proof_mb,
                             max_depth, leaves))


LEAN_LIB = REPO.parent / "local-build" / "adapter" / "lib"
CERTIFY_LIST = REPO / "tools" / "lrat" / "CertifyList.lean"


def lean_emit(inst, cnf):
    """Have Lean build certFormula for the instance file and write its DIMACS form."""
    while psutil.virtual_memory().available < 6 * 2 ** 30:
        time.sleep(10)
    env = dict(os.environ, LEAN_PATH=str(LEAN_LIB))
    proc = subprocess.run([str(LEAN_BIN / "lean.exe"), "-M", "9000", "--run", str(CERTIFY_LIST),
                           "emit", str(inst), str(cnf)], env=env, capture_output=True, text=True)
    return proc.returncode == 0 and cnf.exists(), (proc.stdout + proc.stderr).strip()


def refute_split_lean(stem, code, level_mins, level, q, order, cube, timeout, max_proof_mb,
                      max_depth, leaves):
    """As refute_split, with the formula built and the proof checked by CertifyList.lean."""
    from certify_lean import write_instance
    units = ([(q, True)] if q is not None else []) + cube
    tag = stem + "".join("p" if b else "n" for _, b in cube)
    inst, cnf = WORK / (tag + ".txt"), WORK / (tag + ".cnf")
    write_instance(inst, code, level, level_mins, units)
    ok, msg = lean_emit(inst, cnf)
    if not ok:
        leaves.append({"status": "emit failed: " + msg[:200], "cube": cube})
        print(f"      leaf depth {len(cube)}: emit failed: {msg[:200]}", flush=True)
        return False
    sha = hashlib.sha256(cnf.read_bytes()).hexdigest()
    with open(cnf) as f:
        _, _, nvars, nclauses = f.readline().split()
    env = dict(os.environ, LEAN_PATH=str(LEAN_LIB))
    res = refute_and_check(cnf, timeout, max_proof_mb, env=env, marker="CERTIFIED",
                           checker=lambda lrat: [str(LEAN_BIN / "lean.exe"), "-M", "9000", "--run",
                                                 str(CERTIFY_LIST), "check", str(inst), str(lrat)])
    cnf.unlink(missing_ok=True)
    res.update({"cube": [[int(i), bool(b)] for i, b in cube], "cnf_sha256": sha,
                "instance_sha256": hashlib.sha256(inst.read_bytes()).hexdigest(),
                "variables": int(nvars), "clauses": int(nclauses)})
    inst.unlink(missing_ok=True)
    if res["status"] == "verified":
        leaves.append(res)
        print(f"      leaf depth {len(cube)}: certified (solve {res['solve_seconds']:.0f}s, "
              f"proof {res['proof_bytes'] / 2 ** 20:.0f} MiB, check {res['check_seconds']:.0f}s)",
              flush=True)
        return True
    retry = res["status"].startswith(("refuted, proof", "solver timeout", "CHECK ABORTED"))
    if not retry or len(cube) >= max_depth:
        leaves.append(res)
        print(f"      leaf depth {len(cube)}: {res['status'][:120]}", flush=True)
        return False
    v = order[len(cube)]
    return (refute_split_lean(stem, code, level_mins, level, q, order, cube + [(v, True)],
                              timeout, max_proof_mb, max_depth, leaves)
            and refute_split_lean(stem, code, level_mins, level, q, order, cube + [(v, False)],
                                  timeout, max_proof_mb, max_depth, leaves))


def refute_and_check(cnf, timeout, max_proof_mb, checker=None, marker="VERIFIED UNSAT", env=None):
    """Run CaDiCaL then the Lean checker. Returns a dict describing the outcome."""
    lrat = cnf.with_suffix(".lrat")
    out = {}
    t = time.time()
    solver = subprocess.Popen([str(LEAN_BIN / "cadical.exe"), str(cnf), str(lrat), "--lrat",
                               "--binary=true", "--quiet", "--unsat"],
                              stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    stopped = None
    while solver.poll() is None:  # stop early when the proof is already too large to check
        if time.time() - t > timeout:
            stopped = "solver timeout"
        elif lrat.exists() and lrat.stat().st_size > max_proof_mb * 2 ** 20:
            stopped = "refuted, proof too large to check here (solver stopped)"
        if stopped:
            solver.kill()
            solver.communicate()
            lrat.unlink(missing_ok=True)
            return {"status": stopped, "solve_seconds": time.time() - t}
        time.sleep(0.2)
    stdout = solver.communicate()[0]
    out["solve_seconds"] = time.time() - t
    if "s UNSATISFIABLE" not in stdout:
        return {**out, "status": "not refuted: " + stdout.strip()[:60]}
    out["proof_bytes"] = lrat.stat().st_size
    if out["proof_bytes"] > max_proof_mb * 2 ** 20:
        lrat.unlink()
        return {**out, "status": "refuted, proof too large to check here"}
    if psutil.virtual_memory().available < 8 * 2 ** 30:
        return {**out, "status": "refuted, proof not checked (memory)"}
    t = time.time()
    command = checker(lrat) if checker else [str(LEAN_BIN / "lean.exe"), "-M", "9000", "--run",
                                             str(CHECKER), str(cnf), str(lrat)]
    proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            env=env)
    aborted = False
    while proc.poll() is None:  # never let the checker exhaust the machine's memory
        if psutil.virtual_memory().available < 3 * 2 ** 30:
            proc.kill()
            aborted = True
            break
        time.sleep(0.5)
    stdout, stderr = proc.communicate()
    out["check_seconds"] = time.time() - t
    out["checker_output"] = stdout.strip()
    if aborted or (proc.returncode != 0 and "CHECK FAILED" not in stdout):
        out["status"] = "CHECK ABORTED (memory): " + (stdout + stderr).strip()[:120]
    elif proc.returncode == 0 and marker in stdout:
        out["status"] = "verified"
    else:
        out["status"] = "CHECK FAILED: " + (stdout + stderr).strip()[:200]
    lrat.unlink(missing_ok=True)
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = lambda flag, default: (type(default)(sys.argv[sys.argv.index(flag) + 1])
                                 if flag in sys.argv else default)
    name = args[0]
    code = qec_codes.get(name)
    data = json.loads((HERE / "results" / f"minimal_{name}.json").read_text())
    mins = [tuple(m) for m in data["sets"]]
    w = data["complete"]
    d = min(len(m) for m in mins)
    timeout, max_proof_mb = opt("--timeout", 1200.0), opt("--max-proof-mb", 1500)
    lo, hi = opt("--from", d), opt("--to", w)
    symmetric = "--symmetric" in sys.argv
    max_depth = opt("--split-depth", 0)
    lean_mode = "--lean" in sys.argv
    WORK.mkdir(exist_ok=True)

    # checks by Gaussian elimination, independent of any solver
    exps = [exponent_of(code, m) for m in mins]
    assert all(x > 0 for x in exps), "a listed set is correctable"
    listed = set(mins)
    reps = [None]
    if symmetric:
        group = symmetry_group(code)
        assert all(tuple(sorted(g[i] for i in m)) in listed for g in group for m in mins), \
            "the list is not closed under the symmetry group"
        reps = _orbit_representatives(code.n, group)
    print(f"{code.name}: {len(mins)} listed sets, all uncorrectable, smallest size {d}; "
          f"list complete through {w} according to the SAT search; "
          f"{'symmetric, representatives ' + str(reps) if symmetric else 'plain'}", flush=True)

    path = HERE / "results" / f"certified_{'lean_' if lean_mode else ''}{name}.json"
    record = json.loads(path.read_text()) if path.exists() else {
        "code": code.name, "key": name, "distance": d, "levels": {}}
    record["leading_classes"] = {str(x): sum(1 for m, y in zip(mins, exps)
                                              if len(m) == d and y == x)
                                 for x in sorted(set(exps))
                                 if any(len(m) == d and y == x for m, y in zip(mins, exps))}
    for level in range(lo, hi + 1):
        if record["levels"].get(str(level), {}).get("verified"):
            print(f"  level {level:2d}: already verified", flush=True)
            continue
        parts = []
        for q in reps:
            if lean_mode:
                leaves = []
                t0 = time.time()
                ok_q = refute_split_lean(f"{name}_lean_level{level}_q{q}_", code,
                                         [m for m in mins if len(m) <= level], level, q,
                                         split_order(code, q), [], timeout, max_proof_mb,
                                         max_depth, leaves)
                res = {"status": "verified" if ok_q else "not verified", "representative": q,
                       "formula": "certFormula (Lean)", "leaves": leaves,
                       "solve_seconds": sum(x.get("solve_seconds", 0) for x in leaves),
                       "check_seconds": sum(x.get("check_seconds", 0) for x in leaves),
                       "proof_bytes": sum(x.get("proof_bytes", 0) for x in leaves)}
                parts.append(res)
                print(f"  level {level:2d} q={q}: {res['status']} with {len(leaves)} leaves "
                      f"({time.time() - t0:.0f}s, proofs {res['proof_bytes'] / 2 ** 20:.0f} MiB)",
                      flush=True)
                if not ok_q:
                    break
                continue
            clauses, nvars = instance(code, mins, level, q)
            if max_depth:
                e = _logical_formula(code)[1]
                leaves = []
                t0 = time.time()
                ok_q = refute_split(f"{name}_level{level}_q{q}_", clauses, nvars, e,
                                    split_order(code, q), [], timeout, max_proof_mb, max_depth,
                                    leaves)
                res = {"status": "verified" if ok_q else "not verified", "representative": q,
                       "variables": nvars, "clauses": len(clauses), "leaves": leaves,
                       "solve_seconds": sum(x.get("solve_seconds", 0) for x in leaves),
                       "check_seconds": sum(x.get("check_seconds", 0) for x in leaves),
                       "proof_bytes": sum(x.get("proof_bytes", 0) for x in leaves)}
                parts.append(res)
                print(f"  level {level:2d} q={q}: {res['status']} with {len(leaves)} leaves "
                      f"({time.time() - t0:.0f}s, proofs {res['proof_bytes'] / 2 ** 20:.0f} MiB)",
                      flush=True)
                if not ok_q:
                    break
                continue
            cnf = WORK / f"{name}_level{level}{'' if q is None else '_q' + str(q)}.cnf"
            sha = write_dimacs(cnf, clauses, nvars)
            res = refute_and_check(cnf, timeout, max_proof_mb)
            res.update({"representative": q, "variables": nvars, "clauses": len(clauses),
                        "cnf_sha256": sha})
            parts.append(res)
            print(f"  level {level:2d} q={q}: {res['status']} "
                  f"(solve {res.get('solve_seconds', 0):.0f}s, "
                  f"proof {res.get('proof_bytes', 0) / 2 ** 20:.1f} MiB, "
                  f"check {res.get('check_seconds', 0):.0f}s)", flush=True)
            if res["status"] != "verified":
                break
        ok = all(p["status"] == "verified" for p in parts) and len(parts) == len(reps)
        record["levels"][str(level)] = {"verified": ok, "symmetric": symmetric, "instances": parts}
        if ok:
            record["certified_through"] = max(level, record.get("certified_through", 0))
        path.write_text(json.dumps(record, indent=1))
        if not ok:
            break
    print(f"{code.name}: certified through size {record.get('certified_through')}", flush=True)


if __name__ == "__main__":
    main()
