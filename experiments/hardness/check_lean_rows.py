"""Independent check of check rows exported from the Lean function `reduce`.

Reads blocks "n thr" + rows ("X5 Z7 ...", entries with multiplicity mod 2) separated by "---",
and for each block computes, by exhaustive search over supports of size <= thr + 1, the least
weight of a Pauli in N \\ S (N = symplectic complement of S = row span). Reports whether a
logical of weight <= thr exists, and the minimum weight found up to thr + 1.
"""
import itertools, sys


def parse(path):
    blocks, cur = [], []
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if line.startswith("[check434]") or not line:
            continue
        if line == "---":
            blocks.append(cur); cur = []
        else:
            cur.append(line)
    if cur:
        blocks.append(cur)
    out = []
    for b in blocks:
        n, thr = map(int, b[0].split())
        rows = []
        for line in b[1:]:
            x = z = 0
            for tok in line.split():
                i = int(tok[1:])
                if tok[0] == "X":
                    x ^= 1 << i
                else:
                    z ^= 1 << i
            rows.append((x, z))
        out.append((n, thr, rows))
    return out


def pc(v):
    return bin(v).count("1")


def basis(vecs):
    d = {}
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in d:
                v ^= d[h]
            else:
                d[h] = v
                break
    return d


def in_span(v, d):
    while v:
        h = v.bit_length() - 1
        if h not in d:
            return False
        v ^= d[h]
    return True


def rank(vecs):
    return len(basis(vecs))


def uncorrectable(n, rows, rS, E):
    """Erased set E is uncorrectable iff 2|E| - rank(rows|E) - (rank S - rank(rows|E^c)) > 0."""
    m = sum(1 << q for q in E)
    full = (1 << n) - 1
    c = full ^ m
    rE = rank([(x & m) | ((z & m) << n) for x, z in rows])
    rC = rank([(x & c) | ((z & c) << n) for x, z in rows])
    return 2 * len(E) - rE - (rS - rC) > 0


def analyse(n, thr, rows):
    for (x1, z1) in rows:
        for (x2, z2) in rows:
            assert (pc(x1 & z2) + pc(z1 & x2)) % 2 == 0, "rows do not commute"
    rS = rank([x | (z << n) for x, z in rows])
    k = n - rS
    # monotone: some E of size <= w is uncorrectable iff some E of size exactly w is
    def some(w):
        return any(uncorrectable(n, rows, rS, E) for E in itertools.combinations(range(n), w))
    return k, some(thr), (some(thr + 1) if not some(thr) else None)


if __name__ == "__main__":
    for n, thr, rows in parse(sys.argv[1]):
        k, at_thr, at_thr1 = analyse(n, thr, rows)
        print(f"n={n} thr={thr} rows={len(rows)} k={k} uncorrectable set of size thr: {at_thr}"
              + ("" if at_thr else f"; of size thr+1: {at_thr1}"))
