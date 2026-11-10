"""Brute-force check of a direct CNF -> CSS-code reduction.

Step A (gadget):  CNF phi with N variables and clauses C_1..C_M (K literal
occurrences in total) -> binary system H x = s on 2N + 3K coordinates with
    min{wt x : Hx = s} = N + K      if phi satisfiable,
                      >= N + K + 2   otherwise (or no solution: empty clause).
Step B (quantum): (H, s), duplication m, block length r ->
    CSS code; X-stabilizers: lifted explicit basis of ker H, duplicate pairs,
    adjacent pairs on the block; Z-checks: rows [H' | s_i 1_r].
    distance = min(1 + MLD(H,s), dZ) with dZ >= min(m, r).
Vectors are python ints (bit i = coordinate i).
"""
import itertools, random, sys

popc = lambda v: bin(v).count("1")

def rref_basis(vecs):
    """Return list of independent vectors spanning span(vecs) (xor basis)."""
    basis = {}
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                break
    return list(basis.values())

def in_span(v, basis_dict):
    while v:
        h = v.bit_length() - 1
        if h not in basis_dict:
            return False
        v ^= basis_dict[h]
    return True

def basis_dict(vecs):
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

def nullspace(rows, n):
    """Basis of {x : r.x = 0 for all rows}."""
    # Gaussian elimination on rows
    piv = []  # (col, row)
    R = [r for r in rows]
    red = []
    for r in R:
        for c, pr in red:
            if (r >> c) & 1:
                r ^= pr
        if r:
            c = r.bit_length() - 1
            # eliminate c from earlier
            red = [(c2, (pr ^ r) if (pr >> c) & 1 else pr) for c2, pr in red]
            red.append((c, r))
    pivcols = {c for c, _ in red}
    basis = []
    for f in range(n):
        if f in pivcols:
            continue
        x = 1 << f
        for c, pr in red:
            if (pr >> f) & 1:
                x |= 1 << c
        basis.append(x)
    return basis

def solve_one(rows, rhs, n):
    """Find x with rows[i].x = rhs[i], or None (brute via augmented elimination)."""
    aug = [(r, b) for r, b in zip(rows, rhs)]
    red = []
    for r, b in aug:
        for c, pr, pb in red:
            if (r >> c) & 1:
                r ^= pr; b ^= pb
        if r:
            c = r.bit_length() - 1
            red = [(c2, pr ^ r, pb ^ b) if (pr >> c) & 1 else (c2, pr, pb) for c2, pr, pb in red]
            red.append((c, r, b))
        elif b:
            return None
    x = 0
    for c, pr, pb in red:
        if pb:
            x |= 1 << c
    return x

def min_weight_coset(x0, basis):
    best = popc(x0)
    v = x0
    k = len(basis)
    for i in range(1, 1 << k):
        b = (i & -i).bit_length() - 1
        v ^= basis[b]
        w = popc(v)
        if w < best:
            best = w
    return best

# ---------------- Step A: gadget ----------------
def gadget(N, clauses):
    """clauses: list of lists of (var, neg). Returns rows, rhs, n, coordinate map."""
    idx = {}
    def coord(name):
        if name not in idx:
            idx[name] = len(idx)
        return idx[name]
    for i in range(N):
        coord(("p", i)); coord(("n", i))
    for c, cl in enumerate(clauses):
        for j, _ in enumerate(cl):
            coord(("sig", c, j)); coord(("w", c, j)); coord(("c", c, j))
    rows, rhs = [], []
    for i in range(N):
        rows.append((1 << idx["p", i]) | (1 << idx["n", i])); rhs.append(1)
    for c, cl in enumerate(clauses):
        r = 0
        for j, _ in enumerate(cl):
            r |= 1 << idx["sig", c, j]
        rows.append(r); rhs.append(1)
        for j, (v, neg) in enumerate(cl):
            rows.append((1 << idx["w", c, j]) | (1 << idx["sig", c, j]) | (1 << idx["p", v])); rhs.append(neg)
            rows.append((1 << idx["c", c, j]) | (1 << idx["p", v])); rhs.append(1 ^ neg)
    return rows, rhs, len(idx), idx

def explicit_kernel(N, clauses, idx):
    """Explicit kernel generators of the gadget matrix (no elimination)."""
    gens = []
    for i in range(N):
        v = (1 << idx["p", i]) | (1 << idx["n", i])
        for c, cl in enumerate(clauses):
            for j, (var, _) in enumerate(cl):
                if var == i:
                    v ^= (1 << idx["w", c, j]) | (1 << idx["c", c, j])
        gens.append(v)
    for c, cl in enumerate(clauses):
        for j in range(1, len(cl)):
            gens.append((1 << idx["sig", c, 0]) | (1 << idx["sig", c, j]) |
                        (1 << idx["w", c, 0]) | (1 << idx["w", c, j]))
    return gens

def sat(N, clauses):
    for a in itertools.product([0, 1], repeat=N):
        if all(any(a[v] ^ neg for v, neg in cl) for cl in clauses):
            return True
    return False

def random_cnf(N, M, maxk):
    cls = []
    for _ in range(M):
        k = random.randint(0, maxk) if random.random() < 0.05 else random.randint(1, maxk)
        cls.append([(random.randrange(N), random.randint(0, 1)) for _ in range(k)])
    return cls

def check_gadget(trials, N, M, maxk):
    for _ in range(trials):
        cl = random_cnf(N, M, maxk)
        rows, rhs, n, idx = gadget(N, cl)
        K = sum(len(c) for c in cl)
        ker = nullspace(rows, n)
        gens = explicit_kernel(N, cl, idx)
        # explicit generators lie in kernel and span it
        for g in gens:
            assert all(popc(g & r) % 2 == 0 for r in rows)
        assert len(rref_basis(gens)) == len(ker), "explicit kernel does not span"
        x0 = solve_one(rows, rhs, n)
        S = sat(N, cl)
        if x0 is None:
            assert not S and any(len(c) == 0 for c in cl)
            continue
        mld = min_weight_coset(x0, ker)
        if S:
            assert mld == N + K, (cl, mld, N + K)
        else:
            assert mld >= N + K + 2, (cl, mld, N + K)
    return True

# ---------------- Step B: quantum code ----------------
def quantum_code(rows, rhs, n, kergens, m, r):
    """Return (n', X-generators, Z-generators) for the CSS construction."""
    nq = n * m + r
    lift = lambda v: sum(1 << (j * m) for j in range(n) if (v >> j) & 1)  # copy 0
    def dup_row(rw):
        out = 0
        for j in range(n):
            if (rw >> j) & 1:
                for l in range(m):
                    out |= 1 << (j * m + l)
        return out
    block = sum(1 << (n * m + t) for t in range(r))
    X = [lift(g) for g in kergens]
    X += [(1 << (j * m)) | (1 << (j * m + l)) for j in range(n) for l in range(1, m)]
    X += [(1 << (n * m + t)) | (1 << (n * m + t + 1)) for t in range(r - 1)]
    Z = [dup_row(rw) | (block if b else 0) for rw, b in zip(rows, rhs)]
    for a in X:
        for b in Z:
            assert popc(a & b) % 2 == 0, "stabilizers do not commute"
    return nq, X, Z

def css_side_distance(nq, logical_space_checks, stab):
    """min wt of v with checks.v = 0 and v not in span(stab)."""
    C = nullspace(logical_space_checks, nq)
    Sd = basis_dict(stab)
    # quotient: choose representatives; brute force over C
    best = None
    v = 0
    k = len(C)
    if k > 24:
        raise RuntimeError("too big")
    for i in range(1, 1 << k):
        b = (i & -i).bit_length() - 1
        v ^= C[b]
        w = popc(v)
        if (best is None or w < best) and not in_span(v, Sd):
            best = w
    return best

def generic_distance(nq, gens):
    """Generic stabilizer distance: min symplectic weight of N \\ S, gens as (x,z) pairs."""
    # N = symplectic complement; vectors packed as x | z<<nq
    packed = [x | (z << nq) for x, z in gens]
    swapped = [z | (x << nq) for x, z in gens]  # symplectic form = standard dot with swap
    Nb = nullspace(swapped, 2 * nq)
    Sd = basis_dict(packed)
    mask = (1 << nq) - 1
    best = None
    v = 0
    if len(Nb) > 24:
        raise RuntimeError("too big")
    for i in range(1, 1 << len(Nb)):
        b = (i & -i).bit_length() - 1
        v ^= Nb[b]
        w = popc((v & mask) | (v >> nq))
        if (best is None or w < best) and not in_span(v, Sd):
            best = w
    return best

def dz_formula(rows, rhs, n, x0, m, r):
    best = r
    rb = rref_basis(rows)
    for i in range(1, 1 << len(rb)):
        u = 0
        for t in range(len(rb)):
            if (i >> t) & 1:
                u ^= rb[t]
        if u:
            best = min(best, m * popc(u) + r * (1 ^ (popc(u & x0) % 2)))
    return best

def check_random_HS(trials):
    """Generic (H,s): brute-force stabilizer distance == min(1+MLD, dZ formula)."""
    cnt = 0
    for _ in range(trials):
        n = random.randint(2, 5); mrows = random.randint(1, 4)
        rows = [random.getrandbits(n) for _ in range(mrows)]
        x0 = random.getrandbits(n)
        rhs = [popc(rw & x0) % 2 for rw in rows]
        if not any(rhs):
            continue
        m = random.randint(1, 3); r = random.randint(1, 3)
        if n * m + r > 11:
            continue
        ker = nullspace(rows, n)
        nq, X, Z = quantum_code(rows, rhs, n, ker, m, r)
        gens = [(x, 0) for x in X] + [(0, z) for z in Z]
        d = generic_distance(nq, gens)
        mld = min_weight_coset(x0, ker)
        pred = min(1 + mld, dz_formula(rows, rhs, n, x0, m, r))
        assert d == pred, (rows, rhs, m, r, d, pred)
        assert pred >= min(1 + mld, m, r)
        cnt += 1
    return cnt

def check_full_chain(trials, maxq=48):
    """CNF -> code; distance <= t+1 iff SAT, with m = r = t+2 (t = N+K)."""
    done = 0
    for _ in range(trials * 20):
        if done >= trials:
            break
        N = random.randint(1, 2); M = random.randint(1, 2)
        cl = random_cnf(N, M, 2)
        if any(len(c) == 0 for c in cl):
            continue
        rows, rhs, n, idx = gadget(N, cl)
        K = sum(len(c) for c in cl); t = N + K
        m = r = t + 2
        nq, X, Z = quantum_code(rows, rhs, n, explicit_kernel(N, cl, idx), m, r)
        if nq > maxq:
            continue
        # erasure form: is there a logical (X-type or Z-type; CSS suffices) of
        # weight <= t+1?  Enumerate all supports of size <= t+1 directly.
        S = sat(N, cl)
        Xd, Zd = basis_dict(X), basis_dict(Z)
        found = None
        for w in range(1, t + 2):
            for supp in itertools.combinations(range(nq), w):
                v = sum(1 << q for q in supp)
                if all(popc(v & z) % 2 == 0 for z in Z) and not in_span(v, Xd):
                    found = ("X", w); break
                if all(popc(v & x) % 2 == 0 for x in X) and not in_span(v, Zd):
                    found = ("Z", w); break
            if found:
                break
        assert (found is not None) == S, (cl, found, t, S)
        if S:
            assert found == ("X", t + 1), found  # exactly t+1, X-type
        done += 1
        print(f"  chain ok: clauses={cl} qubits={nq} t+1={t+1} logical<=t+1: {found} sat={S}")
    return done

if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for (N, M, k) in [(2, 2, 3), (3, 3, 3), (3, 5, 3), (4, 6, 2), (4, 8, 3), (5, 10, 3)]:
        check_gadget(300, N, M, k)
        print("gadget ok", N, M, k)
    print("random (H,s) generic-distance checks:", check_random_HS(3000))
    print("full chain checks:", check_full_chain(12))
