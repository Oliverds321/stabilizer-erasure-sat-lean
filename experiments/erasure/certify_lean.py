"""Certify a list of minimal uncorrectable sets with the formula built inside Lean.

usage: python -u certify_lean.py CODE LEVEL [--drop K] [--compare]

For the code CODE (qec_codes.get) and the list results/minimal_CODE.json this

  1. checks by GF(2) arithmetic that the check rows span an isotropic space (the hypothesis
     `hS` of certFormula_checked, which the Lean program does not check);
  2. writes the instance file (format: header of tools/lrat/CertifyList.lean) with the rows of
     `code.h` (column i < n -> `Xi` = `.inl i`, column n + i -> `Zi` = `.inr i`), L = LEVEL and
     the listed sets of size <= LEVEL;
  3. runs `CertifyList.lean emit` (Lean builds `certFormula` and writes DIMACS), CaDiCaL with an
     LRAT proof, and `CertifyList.lean check` (Lean rebuilds the formula and runs the verified
     LRAT checker on it).

The line `CERTIFIED ...` printed by the Lean program means, by
QecPhysical.Stabilizer.Completeness.certFormula_checked (lean/CompletenessFormula.lean):
every uncorrectable erased set of size <= LEVEL contains a listed set.

--drop K   remove the K-th listed set of size <= LEVEL (negative test: the instance should
           then be satisfiable and nothing is certified)
--compare  also build the Python instance of certify.py for the same level and time CaDiCaL
           on it

Temporary files go to ../../../certify_work/lean (outside the repository).
"""
import subprocess
import sys
import time
from pathlib import Path
import json
import os

import numpy as np
import psutil

import qec_codes

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
BIN = REPO.parent / "local-build" / "lean-4.34.1-windows" / "bin"
LIB = REPO.parent / "local-build" / "adapter" / "lib"
PROGRAM = REPO / "tools" / "lrat" / "CertifyList.lean"
WORK = REPO.parent / "certify_work" / "lean"


def isotropic(h):
    n = h.shape[1] // 2
    hx, hz = h[:, :n].astype(np.int64), h[:, n:].astype(np.int64)
    return not ((hx @ hz.T + hz @ hx.T) % 2).any()


def write_instance(path, code, level, mins, units=()):
    h = np.array(code.h, dtype=np.uint8) % 2
    n = code.n
    lines = [f"# {code.name}, level {level}", f"n {n}", f"L {level}"]
    for row in h:
        coords = [f"X{i}" for i in range(n) if row[i]] + [f"Z{i}" for i in range(n) if row[n + i]]
        lines.append("row " + " ".join(coords))
    lines += ["min " + " ".join(map(str, m)) for m in mins]
    lines += [f"unit {q} {int(b)}" for q, b in units]
    path.write_text("\n".join(lines) + "\n", newline="\n")


def lean(mode, *files):
    env = dict(os.environ, LEAN_PATH=str(LIB))
    if psutil.virtual_memory().available < 6 * 2 ** 30:
        sys.exit("REFUSED: less than 6 GiB free; wait and retry")
    t = time.time()
    proc = subprocess.run([str(BIN / "lean.exe"), "-M", "9000", "--run", str(PROGRAM), mode,
                           *map(str, files)], env=env, capture_output=True, text=True)
    return proc.returncode, (proc.stdout + proc.stderr).strip(), time.time() - t


def cadical(cnf, lrat=None):
    t = time.time()
    cmd = [str(BIN / "cadical.exe"), str(cnf)]
    cmd += [str(lrat), "--lrat", "--binary=true", "--quiet", "--unsat"] if lrat else ["-q"]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    status = ("UNSAT" if "s UNSATISFIABLE" in out else
              "SAT" if "s SATISFIABLE" in out else "UNKNOWN")
    return status, time.time() - t


def header(cnf):
    with open(cnf) as f:
        _, _, v, c = f.readline().split()
    return int(v), int(c)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    name, level = args[0], int(args[1])
    drop = int(sys.argv[sys.argv.index("--drop") + 1]) if "--drop" in sys.argv else None
    if drop is not None:
        args = args[:2]
    code = qec_codes.get(name)
    data = json.loads((HERE / "results" / f"minimal_{name}.json").read_text())
    mins = [list(m) for m in data["sets"] if len(m) <= level]
    tag = f"{name}_L{level}"
    if drop is not None:
        print(f"negative test: dropping listed set {mins[drop]}")
        mins = mins[:drop] + mins[drop + 1:]
        tag += f"_drop{drop}"
    h = np.array(code.h, dtype=np.uint8) % 2
    assert isotropic(h), "the check rows are not isotropic"
    WORK.mkdir(parents=True, exist_ok=True)
    inst, cnf, lrat = WORK / f"{tag}.txt", WORK / f"{tag}.cnf", WORK / f"{tag}.lrat"
    write_instance(inst, code, level, mins)
    print(f"{code.name}: n={code.n}, {h.shape[0]} rows, {len(mins)} listed sets of size <= {level}"
          f" (list complete through {data['complete']} according to the SAT search)")

    rc, out, t_emit = lean("emit", inst, cnf)
    print(f"  emit  ({t_emit:.1f}s): {out}")
    if rc:
        sys.exit(1)
    nv, nc = header(cnf)
    status, t_solve = cadical(cnf, lrat)
    print(f"  Lean formula: {nv} variables, {nc} clauses; CaDiCaL {status} in {t_solve:.2f}s"
          + (f", proof {lrat.stat().st_size / 2 ** 20:.2f} MiB" if lrat.exists() else ""))
    if status == "UNSAT":
        rc, out, t_check = lean("check", inst, lrat)
        print(f"  check ({t_check:.1f}s): {out}")
    else:
        print("  NOT CERTIFIED (the formula is not refuted)")
        rc = 1
    lrat.unlink(missing_ok=True)

    if "--compare" in sys.argv:
        from certify import instance, write_dimacs
        clauses, nvars = instance(code, [tuple(m) for m in mins], level)
        pcnf = WORK / f"{tag}_python.cnf"
        write_dimacs(pcnf, clauses, nvars)
        plrat = pcnf.with_suffix(".lrat")
        pstatus, pt = cadical(pcnf, plrat)
        print(f"  Python formula: {nvars} variables, {len(clauses)} clauses; CaDiCaL {pstatus} in "
              f"{pt:.2f}s" + (f", proof {plrat.stat().st_size / 2 ** 20:.2f} MiB"
                              if plrat.exists() else ""))
        plrat.unlink(missing_ok=True)
    sys.exit(rc)


if __name__ == "__main__":
    main()
