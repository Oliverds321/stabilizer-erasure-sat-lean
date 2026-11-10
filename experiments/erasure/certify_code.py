"""Combine everything into one Lean-checked certificate per code.

usage: python -u certify_code.py CODE [--level L] [--neg KIND] [--full]

Writes a bundle (format: header of tools/lrat/CertifyCode.lean) from
results/minimal_CODE.json, results/certified_lean_CODE.json and qec_codes/hybrid, runs
`CertifyCode.lean combine BUNDLE`, and stores results/certificate_CODE.json.

The bundle carries:
  * the check rows (from code.h, as certify_lean.write_instance writes them),
  * the listed sets of size <= L (same order as in the CertifyList instance files),
  * uncorrectability certificates (x in N supported on the set, z a logical operator with
    <x, z> = 1), found here by GF(2) elimination and *checked* in Lean,
  * with symmetry: the generators (code.generators), for each generator the image index of every
    listed set, and for every qubit a word in the generators moving it to a representative
    (BFS), all checked in Lean,
  * the leaves (representative, unit literals, recorded instance SHA-256).

What Lean checks and what its CERTIFIED line means is stated in tools/lrat/CertifyCode.lean
(theorems symmetric_certificate / plain_certificate of lean/ListCertificate.lean). Nothing
decided here is trusted: a wrong certificate, image table, word or leaf list makes the Lean
check fail.

--full      re-create the leaf proofs (CertifyList emit + CaDiCaL, files under
            ../../../certify_work/code) and run `CertifyCode.lean full`, which checks every
            leaf proof against certFormula itself (no hash records involved)
--neg KIND  negative tests (nothing must be certified):
    correctable  add a correctable set of size d to the list
    generator    replace the first generator by a transposition of qubits 0 and 1
    leaf         drop the last leaf (or, with a single leaf, replace it by the cube [0 erased])
    closure      remove the image of listed set 0 under the first generator from the list
"""
import hashlib
import itertools
import json
import os
import subprocess
import sys
import time
from collections import deque
from pathlib import Path

import numpy as np
import psutil

import qec_codes
from gf2 import nullspace_dense
from hybrid import symmetry_group

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
BIN = REPO.parent / "local-build" / "lean-4.34.1-windows" / "bin"
LIB = REPO.parent / "local-build" / "adapter" / "lib"
PROGRAM = REPO / "tools" / "lrat" / "CertifyCode.lean"
WORK = REPO.parent / "certify_work" / "code"


def coords(vec, n):
    return [f"X{i}" for i in range(n) if vec[i]] + [f"Z{i}" for i in range(n) if vec[n + i]]


def certificate(h, logicals, m, n):
    """x in N supported on m and the index j of a logical z with <x, z> = 1, or None."""
    m = list(m)
    # unknowns: x_X[i], x_Z[i] for i in m; constraint <row, x> = row_X . x_Z + row_Z . x_X
    a = np.concatenate([h[:, [n + i for i in m]], h[:, m]], axis=1) % 2
    for v in nullspace_dense(a):
        x = np.zeros(2 * n, dtype=np.uint8)
        for t, i in enumerate(m):
            x[i] = v[t]
            x[n + i] = v[len(m) + t]
        for j, z in enumerate(logicals):
            if (int(x[:n] @ z[n:]) + int(x[n:] @ z[:n])) % 2 == 1:
                return x, j
    return None


def words_to_reps(gens, reps, n):
    """For every qubit a word (rightmost generator first) moving it into reps."""
    words = []
    for i in range(n):
        seen, queue = {i: []}, deque([i])
        while queue:
            j = queue.popleft()
            if j in reps:
                break
            for k, g in enumerate(gens):
                if g[j] not in seen:
                    seen[g[j]] = seen[j] + [k]
                    queue.append(g[j])
        target = next(j for j in seen if j in reps)
        words.append(list(reversed(seen[target])))
    return words


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    name = args[0]
    neg = sys.argv[sys.argv.index("--neg") + 1] if "--neg" in sys.argv else None
    if neg:
        args = args[:1]
    code = qec_codes.get(name)
    n = code.n
    h = np.array(code.h, dtype=np.uint8) % 2
    data = json.loads((HERE / "results" / f"minimal_{name}.json").read_text())
    rec = json.loads((HERE / "results" / f"certified_lean_{name}.json").read_text())
    level = (int(sys.argv[sys.argv.index("--level") + 1]) if "--level" in sys.argv
             else max(int(k) for k, v in rec["levels"].items() if v["verified"]))
    lv = rec["levels"][str(level)]
    assert lv["verified"], f"level {level} not verified by certify.py --lean"
    mins = [list(m) for m in data["sets"] if len(m) <= level]
    d = min(len(m) for m in mins)
    symmetric = lv["symmetric"]
    leaves = [(inst["representative"], leaf["instance_sha256"], leaf["cube"])
              for inst in lv["instances"] for leaf in inst["leaves"]]
    reps = sorted({r for r, _, _ in leaves if r is not None})
    gens = [list(map(int, g)) for g in code.generators] if symmetric else []
    words = words_to_reps(gens, set(reps), n) if symmetric else []

    if neg == "correctable":
        listed = {frozenset(m) for m in mins}
        extra = next(list(c) for c in itertools.combinations(range(n), d)
                     if not any(frozenset(m) <= frozenset(c) for m in listed))
        mins.append(extra)
        print(f"negative test: added the correctable set {extra}")
    if neg == "generator":
        gens[0] = [1, 0] + list(range(2, n))
        print("negative test: first generator replaced by the transposition (0 1)")
    if neg == "leaf":
        last_rep = leaves[-1][0]
        if sum(1 for r, _, _ in leaves if r == last_rep) > 1:
            print(f"negative test: dropped leaf {leaves[-1][2]} of representative {last_rep}")
            leaves = leaves[:-1]
        else:
            v = next(q for q in range(n) if q != last_rep)
            leaves = leaves[:-1] + [(last_rep, leaves[-1][1], [[v, True]])]
            print(f"negative test: the only leaf of representative {last_rep} replaced by the "
                  f"cube [qubit {v} erased] (the case 'qubit {v} not erased' is missing)")

    logicals = np.array(code.logical_basis(), dtype=np.uint8) % 2
    t = time.time()
    certs = []
    for k, m in enumerate(mins):
        c = certificate(h, logicals, m, n)
        if c is not None:
            certs.append((k, c[1], coords(c[0], n)))
    print(f"{code.name} level {level}: {len(mins)} listed sets, {len(certs)} certificates "
          f"({time.time() - t:.1f}s), d={d}, {'symmetric' if symmetric else 'plain'}, "
          f"{len(leaves)} leaves")

    index = {frozenset(m): k for k, m in enumerate(mins)}
    imgs = []
    for g in gens:
        imgs.append([index.get(frozenset(g[i] for i in m), len(mins)) for m in mins])
    if neg == "closure":
        target = index[frozenset(gens[0][i] for i in mins[0])]
        print(f"negative test: removed listed set {mins[target]} (image of set 0)")
        # keep every other table entry pointing at the same set after the removal
        mins = mins[:target] + mins[target + 1:]
        certs = [(k - (k > target), j, x) for k, j, x in certs if k != target]
        index = {frozenset(m): k for k, m in enumerate(mins)}
        imgs = [[index.get(frozenset(g[i] for i in m), len(mins)) for m in mins] for g in gens]

    lines = [f"name {code.name}", f"n {n}", f"L {level}", f"d {d}"]
    lines += ["row " + " ".join(coords(r, n)) for r in h]
    lines += ["min " + " ".join(map(str, m)) for m in mins]
    lines += ["logical " + " ".join(coords(z, n)) for z in logicals]
    lines += [f"cert {k} {j} " + " ".join(x) for k, j, x in certs]
    for g, img in zip(gens, imgs):
        lines += ["gen " + " ".join(map(str, g)), "img " + " ".join(map(str, img))]
    lines += [f"word {i} " + " ".join(map(str, w)) for i, w in enumerate(words)]
    for r, sha, cube in leaves:
        lits = " ".join(f"{v}:{int(b)}" for v, b in cube)
        lines.append(f"leaf {'-' if r is None else r} {sha} {lits}".rstrip())
    WORK.mkdir(parents=True, exist_ok=True)
    bundle = WORK / f"{name}_L{level}{'_neg_' + neg if neg else ''}.txt"
    bundle.write_text("\n".join(lines) + "\n", newline="\n")

    mode = ["combine", str(bundle)]
    if "--full" in sys.argv:
        # re-create every leaf proof: CertifyList emit (Lean builds the formula), CaDiCaL
        from certify_lean import write_instance
        proofs = WORK / f"{name}_L{level}_proofs"
        proofs.mkdir(exist_ok=True)
        for k, (r, _, cube) in enumerate(leaves):
            units = ([(r, True)] if r is not None else []) + [(v, b) for v, b in cube]
            inst, cnf = proofs / f"leaf{k}.txt", proofs / f"leaf{k}.cnf"
            write_instance(inst, code, level, mins, units)
            subprocess.run([str(BIN / "lean.exe"), "-M", "9000", "--run",
                            str(REPO / "tools" / "lrat" / "CertifyList.lean"), "emit", str(inst),
                            str(cnf)], env=dict(os.environ, LEAN_PATH=str(LIB)), check=True,
                           capture_output=True)
            subprocess.run([str(BIN / "cadical.exe"), str(cnf), str(proofs / f"leaf{k}.lrat"),
                            "--lrat", "--binary=true", "--quiet", "--unsat"], capture_output=True)
            cnf.unlink()
        mode = ["full", str(bundle), str(proofs)]
    while psutil.virtual_memory().available < 6 * 2 ** 30:
        print("waiting for memory", flush=True)
        time.sleep(30)
    t = time.time()
    proc = subprocess.run([str(BIN / "lean.exe"), "-M", "9000", "--run", str(PROGRAM), *mode],
                          env=dict(os.environ, LEAN_PATH=str(LIB)),
                          capture_output=True, text=True)
    out = (proc.stdout + proc.stderr).strip()
    seconds = time.time() - t
    print(out)
    certified = proc.returncode == 0 and "CERTIFIED CODE" in out
    print(f"[{seconds:.0f}s] {'CERTIFIED' if certified else 'NOT CERTIFIED'}")
    if not neg and "--full" not in sys.argv:
        result = {"code": code.name, "key": name, "level": level, "distance": d,
                  "symmetric": symmetric, "listed": len(mins), "leaves": len(leaves),
                  "certified": certified, "lean_output": out, "seconds": seconds,
                  "bundle_sha256": hashlib.sha256(bundle.read_bytes()).hexdigest(),
                  "program": "tools/lrat/CertifyCode.lean combine",
                  "meaning": "lean/ListCertificate.lean: symmetric_certificate / "
                             "plain_certificate (Certified rows L d mins)"}
        (HERE / "results" / f"certificate_{name}.json").write_text(json.dumps(result, indent=1))
    sys.exit(0 if certified == (neg is None) else 1)


if __name__ == "__main__":
    main()
