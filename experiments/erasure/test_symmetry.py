"""The symmetry-reduced, parallel enumeration of minimal uncorrectable sets must
return exactly the same list as the plain enumeration."""
import sys
import time

import qec_codes
from hybrid import minimal_sets, symmetry_group

if __name__ == "__main__":
    ok = True
    quiet = lambda *a: None
    for name, w in [("toric3", 6), ("toric4", 10), ("bb72", 11), ("surface5", 8)]:
        code = qec_codes.get(name)
        t = time.time()
        plain, cp = minimal_sets(code, w, log=quiet, use_symmetry=False)
        tp = time.time() - t
        t = time.time()
        sym, cs = minimal_sets(code, w, log=quiet, name=name)
        ts = time.time() - t
        same = sorted(plain) == sorted(sym) and cp == cs
        ok &= same
        print(f"{code.name:26s} group order {len(symmetry_group(code)):3d}  plain {len(plain):6d} sets "
              f"{tp:6.1f}s   symmetric {len(sym):6d} sets {ts:6.1f}s   "
              f"{'identical' if same else 'DIFFERENT'}", flush=True)
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
