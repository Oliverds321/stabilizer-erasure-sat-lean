"""Stabilizer codes as binary check matrices H = (HX | HZ), one row per check.

Every constructor returns a `Code` whose rows are checked to commute. Nothing
here is specific to the estimator; see `gf2.py` for ranks and `certificates.py`
for the SAT encodings.
"""
from dataclasses import dataclass
from itertools import product

import numpy as np

from gf2 import rank_dense, nullspace_dense


@dataclass
class Code:
    name: str
    hx: np.ndarray  # m x n, X-part of every check
    hz: np.ndarray  # m x n, Z-part of every check
    generators: tuple = ()  # candidate qubit permutations (verified in hybrid.symmetry_group)

    @property
    def n(self):
        return self.hx.shape[1]

    @property
    def m(self):
        return self.hx.shape[0]

    @property
    def h(self):
        return np.concatenate([self.hx, self.hz], axis=1).astype(np.uint8)

    @property
    def s(self):
        return rank_dense(self.h)

    @property
    def k(self):
        return self.n - self.s

    @property
    def nnz(self):
        return int(self.hx.sum() + self.hz.sum())

    def check(self):
        comm = (self.hx @ self.hz.T + self.hz @ self.hx.T) % 2
        if comm.any():
            raise ValueError(f"{self.name}: checks do not commute")
        return self

    def normalizer_basis(self):
        """Rows spanning N = S^perp, as (2k+s) x 2n matrix in (X | Z) layout."""
        swapped = np.concatenate([self.hz, self.hx], axis=1)  # h Lambda
        return nullspace_dense(swapped)

    def logical_basis(self):
        """2k rows of N that are independent modulo S."""
        basis = [r for r in _row_basis(self.h)]
        out = []
        for v in self.normalizer_basis():
            if rank_dense(np.array(basis + [v], dtype=np.uint8)) > len(basis):
                basis.append(v)
                out.append(v)
        out = np.array(out, dtype=np.uint8).reshape(-1, 2 * self.n)
        assert out.shape[0] == 2 * self.k
        return out


def _row_basis(mat):
    basis = []
    for r in mat:
        if rank_dense(np.array(basis + [r], dtype=np.uint8)) > len(basis):
            basis.append(r)
    return basis


def css(name, hx_checks, hz_checks):
    hx_checks = np.array(hx_checks, dtype=np.uint8) % 2
    hz_checks = np.array(hz_checks, dtype=np.uint8) % 2
    n = hx_checks.shape[1]
    hx = np.concatenate([hx_checks, np.zeros((hz_checks.shape[0], n), np.uint8)])
    hz = np.concatenate([np.zeros((hx_checks.shape[0], n), np.uint8), hz_checks])
    return Code(name, hx, hz).check()


def from_paulis(name, strings):
    hx = np.array([[c in "XY" for c in s] for s in strings], dtype=np.uint8)
    hz = np.array([[c in "ZY" for c in s] for s in strings], dtype=np.uint8)
    return Code(name, hx, hz).check()


def five_qubit():
    return from_paulis("[[5,1,3]]", ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"])


def steane():
    hmat = [[1, 0, 1, 0, 1, 0, 1], [0, 1, 1, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1, 1]]
    return css("Steane [[7,1,3]]", hmat, hmat)


def shor9():
    hz = [[1, 1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0],
          [0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1]]
    hx = [[1, 1, 1, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 1, 1, 1, 1]]
    return css("Shor [[9,1,3]]", hx, hz)


def repetition_classical(length):
    return np.array([[1 if j in (i, (i + 1) % length) else 0 for j in range(length)]
                     for i in range(length)], dtype=np.uint8)


def hypergraph_product(name, h1, h2):
    h1 = np.array(h1, dtype=np.uint8)
    h2 = np.array(h2, dtype=np.uint8)
    m1, n1 = h1.shape
    m2, n2 = h2.shape
    hx = np.concatenate([np.kron(h1, np.eye(n2, dtype=np.uint8)),
                         np.kron(np.eye(m1, dtype=np.uint8), h2.T)], axis=1)
    hz = np.concatenate([np.kron(np.eye(n1, dtype=np.uint8), h2),
                         np.kron(h1.T, np.eye(m2, dtype=np.uint8))], axis=1)
    return css(name, hx % 2, hz % 2)


def _two_block_shifts(l, m):
    """Translations of two l x m blocks of qubits indexed block*l*m + a*m + b."""
    idx = lambda blk, a, b: blk * l * m + (a % l) * m + (b % m)
    g1 = [idx(blk, a + 1, b) for blk in (0, 1) for a in range(l) for b in range(m)]
    g2 = [idx(blk, a, b + 1) for blk in (0, 1) for a in range(l) for b in range(m)]
    return (tuple(g1), tuple(g2))


def toric(size):
    rep = repetition_classical(size)
    code = hypergraph_product(f"toric [[{2 * size * size},2,{size}]]", rep, rep)
    code.generators = _two_block_shifts(size, size)
    return code


def rotated_surface(d):
    """Rotated surface code [[d^2, 1, d]] with qubits on a d x d grid."""
    q = lambda r, c: r * d + c
    xs, zs = [], []
    for r in range(-1, d):
        for c in range(-1, d):
            cells = [(r + a, c + b) for a in (0, 1) for b in (0, 1)
                     if 0 <= r + a < d and 0 <= c + b < d]
            if len(cells) < 2:
                continue
            is_x = (r + c) % 2 == 0
            if len(cells) == 2:
                top_or_bottom = r in (-1, d - 1)
                if top_or_bottom != is_x:
                    continue
            row = [0] * (d * d)
            for cell in cells:
                row[q(*cell)] = 1
            (xs if is_x else zs).append(row)
    return css(f"rotated surface [[{d * d},1,{d}]]", xs, zs)


def bivariate_bicycle(l, m, a_terms, b_terms, label):
    """Bravyi et al. (2024). Terms are ('x', e) or ('y', e)."""
    def shift(size):
        return np.roll(np.eye(size, dtype=np.uint8), 1, axis=1)
    x = np.kron(shift(l), np.eye(m, dtype=np.uint8))
    y = np.kron(np.eye(l, dtype=np.uint8), shift(m))
    def poly(terms):
        acc = np.zeros((l * m, l * m), dtype=np.uint8)
        for var, e in terms:
            acc = (acc + np.linalg.matrix_power(x if var == "x" else y, e)) % 2
        return acc
    a, b = poly(a_terms), poly(b_terms)
    hx = np.concatenate([a, b], axis=1)
    hz = np.concatenate([b.T, a.T], axis=1)
    code = css(label, hx, hz)
    code.generators = _two_block_shifts(l, m)
    return code


def bb72():
    return bivariate_bicycle(6, 6, [("x", 3), ("y", 1), ("y", 2)],
                             [("y", 3), ("x", 1), ("x", 2)], "BB [[72,12,6]]")


def bb90():
    return bivariate_bicycle(15, 3, [("x", 9), ("y", 1), ("y", 2)],
                             [("x", 0), ("x", 2), ("x", 7)], "BB [[90,8,10]]")


def bb108():
    return bivariate_bicycle(9, 6, [("x", 3), ("y", 1), ("y", 2)],
                             [("y", 3), ("x", 1), ("x", 2)], "BB [[108,8,10]]")


def bb144():
    return bivariate_bicycle(12, 6, [("x", 3), ("y", 1), ("y", 2)],
                             [("y", 3), ("x", 1), ("x", 2)], "BB [[144,12,12]]")


def hamming_css(r):
    cols = [list(map(int, np.binary_repr(i, r))) for i in range(1, 2 ** r)]
    hmat = np.array(cols, dtype=np.uint8).T
    return css(f"Hamming CSS [[{2 ** r - 1},{2 ** r - 1 - 2 * r},3]]", hmat, hmat)


def ashikhmin12():
    """The [[12,6]] code of Example 1 of Ashikhmin (ISIT 2020, doi 10.1109/ISIT44484.2020.9174340).

    Its stabilizer is the F_4-span of three rows; with 0, 1, w, w^2 written I, X, Z, Y the
    binary generators are each row and w times it (X -> Z, Z -> Y, Y -> X). Its distance is 3.
    """
    rows = ["XIIIIXXXXXXX", "IXIXXIIXZZZY", "IIXXZXZIIXYX"]
    times_w = str.maketrans("XZY", "ZYX")
    return from_paulis("Ashikhmin [[12,6,3]]", [r for g in rows for r in (g, g.translate(times_w))])


REGISTRY = {
    "five": five_qubit, "steane": steane, "shor9": shor9,
    "surface3": lambda: rotated_surface(3), "surface5": lambda: rotated_surface(5),
    "surface7": lambda: rotated_surface(7), "surface9": lambda: rotated_surface(9),
    "toric3": lambda: toric(3), "toric4": lambda: toric(4), "toric5": lambda: toric(5),
    "toric6": lambda: toric(6), "toric8": lambda: toric(8),
    "hamming15": lambda: hamming_css(4),
    "ashikhmin12": ashikhmin12,
    "bb72": bb72, "bb90": bb90, "bb108": bb108, "bb144": bb144,
}


def get(name):
    return REGISTRY[name]()


if __name__ == "__main__":
    for key in REGISTRY:
        c = get(key)
        print(f"{key:10s} {c.name:28s} n={c.n:4d} k={c.k:3d} checks={c.m:4d} nnz={c.nnz}")
