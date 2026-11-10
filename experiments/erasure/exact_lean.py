"""Exact coefficient tables computed by the verified Lean function, compared with Python.

usage: python -u exact_lean.py CODE [CODE ...]

For each code (qec_codes.get) this

  1. writes the check rows in the instance format of tools/lrat/CertifyList.lean
     (certify_lean.write_instance, with no listed sets);
  2. runs `lean --run tools/exact/ExactTable.lean INSTANCE` (the program prints
     f_j = fRat rows j and u_j = uRat rows j, which by
     QecPhysical.Stabilizer.ExactTable.fRat_spec / uRat_spec in lean/ExactTable.lean are
     layerAverage id (erasureScore (rowSpace rows)) j and layerFraction (rowSpace rows) j);
  3. saves results/exact_lean_CODE.json and compares it entry by entry, as exact fractions,
     with results/exact_CODE.json (written by curves.exact_tables).

Temporary files go to ../../../certify_work/exact (outside the repository).
"""
import json
import os
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

import psutil

import qec_codes
from certify_lean import write_instance

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
BIN = REPO.parent / "local-build" / "lean-4.34.1-windows" / "bin"
LIB = REPO.parent / "local-build" / "adapter" / "lib"
PROGRAM = REPO / "tools" / "exact" / "ExactTable.lean"
WORK = REPO.parent / "certify_work" / "exact"


def run(name, timeout):
    code = qec_codes.get(name)
    WORK.mkdir(parents=True, exist_ok=True)
    inst = WORK / f"{name}.txt"
    write_instance(inst, code, 0, [])
    if psutil.virtual_memory().available < 6 * 2 ** 30:
        sys.exit("REFUSED: less than 6 GiB free; wait and retry")
    env = dict(os.environ, LEAN_PATH=str(LIB))
    t = time.time()
    proc = subprocess.run([str(BIN / "lean.exe"), "-M", "9000", "--run", str(PROGRAM), str(inst)],
                          env=env, capture_output=True, text=True, timeout=timeout)
    seconds = time.time() - t
    if proc.returncode:
        sys.exit(f"{name}: Lean program failed:\n{proc.stdout}{proc.stderr}")
    f, u = {}, {}
    for line in proc.stdout.splitlines():
        parts = line.split()
        if parts and parts[0] in ("f", "u"):
            (f if parts[0] == "f" else u)[int(parts[1])] = Fraction(parts[2])
    n = code.n
    assert sorted(f) == list(range(n + 1)) and sorted(u) == list(range(n + 1)), "incomplete output"
    out = {"code": code.name, "n": n, "source": "lean/ExactTable.lean (fRat, uRat)",
           "f": [str(f[j]) for j in range(n + 1)], "u": [str(u[j]) for j in range(n + 1)],
           "seconds": round(seconds, 1)}
    ref_path = HERE / "results" / f"exact_{name}.json"
    if ref_path.exists():
        ref = json.loads(ref_path.read_text())
        bad = [("f", j) for j in range(n + 1) if Fraction(ref["f"][j]) != f[j]]
        bad += [("u", j) for j in range(n + 1) if Fraction(ref["u"][j]) != u[j]]
        out["matches_python"] = not bad
        out["mismatches"] = [f"{k}_{j}" for k, j in bad]
    (HERE / "results" / f"exact_lean_{name}.json").write_text(json.dumps(out) + "\n")
    status = ("MATCH" if out.get("matches_python") else
              f"MISMATCH {out['mismatches']}" if "matches_python" in out else "no reference")
    print(f"{code.name}: n={n}, 2^n={2 ** n} sets, Lean {seconds:.1f}s, {status}")
    return out


def main():
    timeout = int(sys.argv[sys.argv.index("--timeout") + 1]) if "--timeout" in sys.argv else 3600
    names = [a for i, a in enumerate(sys.argv[1:], 1)
             if not a.startswith("--") and sys.argv[i - 1] != "--timeout"]
    ok = True
    for name in names:
        ok &= bool(run(name, timeout).get("matches_python", False))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
