"""The two projected certificates of the paper as 3-CNF formulas.

For a check matrix H = (HX | HZ) and a layer j, `layer_formula` builds the
3-CNF of Lemma "Linear incidence":

    variables   E (n bits), z = (zX, zZ) (2n bits), existential witnesses
    constraints |E| = j,  z in N,  and  Good(E, z)  or  Bad(E, z)

    Good(E, z):  exists u in F_2^m with (z + uH)|_E = 0
    Bad(E, z):   exists x in N supported on E with <x, z>_s = 1

The number of distinct assignments to the projection bits (E, z) is

    A_j = sum_{|E|=j} |N| 2^{-d_E}     (Good)
    B_j = sum_{|E|=j} |N| (1 - 2^{-d_E})   (Bad)

`reduced=True` replaces z by its logical class a in F_2^{2k} (z = sum a_i L_i
for a fixed basis L of N modulo S). Good and Bad depend on z only through that
class, so the projected counts become 4^k 2^{-d_E} and 4^k (1 - 2^{-d_E}) per
erased set. This needs a logical basis, which the paper's version avoids, and
it shortens the projection from 3n to n + 2k bits.

Every XOR is a chain of two-input gates with full-equivalence Tseitin clauses,
and the cardinality constraint is a totalizer, so every clause has width at
most three.
"""
from dataclasses import dataclass, field

import numpy as np
from pysat.card import CardEnc, EncType


@dataclass
class Formula:
    clauses: list = field(default_factory=list)
    nvars: int = 0

    def new(self, count=1):
        first = self.nvars + 1
        self.nvars += count
        return list(range(first, first + count))

    def add(self, *lits):
        self.clauses.append(list(lits))

    def xor2(self, a, b):
        t = self.new()[0]
        self.add(-a, -b, -t)
        self.add(a, b, -t)
        self.add(a, -b, t)
        self.add(-a, b, t)
        return t

    def and2(self, a, b):
        t = self.new()[0]
        self.add(-a, -b, t)
        self.add(a, -t)
        self.add(b, -t)
        return t

    def xor_chain(self, lits):
        """Variable equal to the XOR of `lits` (None if the list is empty)."""
        if not lits:
            return None
        acc = lits[0]
        for lit in lits[1:]:
            acc = self.xor2(acc, lit)
        return acc

    def xor_equals(self, lits, rhs):
        t = self.xor_chain(lits)
        if t is None:
            if rhs:
                self.add()  # empty clause: unsatisfiable
            return
        self.add(t if rhs else -t)

    def exactly(self, lits, bound):
        if bound == 0:
            for lit in lits:
                self.add(-lit)
            return
        if bound == len(lits):
            for lit in lits:
                self.add(lit)
            return
        enc = CardEnc.equals(lits=lits, bound=bound, top_id=self.nvars,
                             encoding=EncType.totalizer)
        self.nvars = max(self.nvars, enc.nv)
        for clause in enc.clauses:
            self.add_split(clause)

    def add_split(self, clause):
        """Add a clause, splitting it into width-three pieces with fresh links."""
        clause = list(clause)
        while len(clause) > 3:
            link = self.new()[0]
            self.add(clause[0], clause[1], link)
            clause = [-link] + clause[2:]
        self.add(*clause)

    @property
    def width(self):
        return max((len(c) for c in self.clauses), default=0)


def _normalizer_constraints(f, code, vx, vz):
    """(vx, vz) commutes with every check."""
    for r in range(code.m):
        lits = [vz[i] for i in range(code.n) if code.hx[r, i]]
        lits += [vx[i] for i in range(code.n) if code.hz[r, i]]
        f.xor_equals(lits, 0)


def layer_formula(code, j, kind, reduced=False, exact_size=True):
    """Return (formula, projection variables) for layer j and kind in {'good','bad'}."""
    n, m = code.n, code.m
    f = Formula()
    e = f.new(n)
    if reduced:
        basis = code.logical_basis()
        a = f.new(basis.shape[0])
        zx = [f.xor_chain([a[t] for t in range(len(a)) if basis[t, i]]) for i in range(n)]
        zz = [f.xor_chain([a[t] for t in range(len(a)) if basis[t, n + i]]) for i in range(n)]
        projection = e + a
    else:
        zx, zz = f.new(n), f.new(n)
        _normalizer_constraints(f, code, zx, zz)
        projection = e + zx + zz
    if exact_size:
        f.exactly(e, j)
    if kind == "good":
        u = f.new(m)
        for i in range(n):
            for part, zvar in ((code.hx, zx[i]), (code.hz, zz[i])):
                lits = [u[r] for r in range(m) if part[r, i]]
                if zvar is not None:
                    lits.append(zvar)
                t = f.xor_chain(lits)
                if t is not None:
                    f.add(-e[i], -t)  # erased qubit: (z + uH) vanishes there
    elif kind == "bad":
        xx, xz = f.new(n), f.new(n)
        _normalizer_constraints(f, code, xx, xz)
        terms = []
        for i in range(n):
            f.add(-xx[i], e[i])
            f.add(-xz[i], e[i])
            if zz[i] is not None:
                terms.append(f.and2(xx[i], zz[i]))
            if zx[i] is not None:
                terms.append(f.and2(xz[i], zx[i]))
        f.xor_equals(terms, 1)
    else:
        raise ValueError(kind)
    return f, projection


def uncorrectable_formula(code, j, at_most=False):
    """Erased sets E with d_E > 0: project the Bad certificate onto E only."""
    f, projection = layer_formula(code, j, "bad", reduced=False, exact_size=False)
    e = projection[:code.n]
    if at_most:
        enc = CardEnc.atmost(lits=e, bound=j, top_id=f.nvars, encoding=EncType.totalizer)
        f.nvars = max(f.nvars, enc.nv)
        for clause in enc.clauses:
            f.add_split(clause)
    else:
        f.exactly(e, j)
    return f, e


def enumerate_projected(formula, projection, limit=None, time_limit=None):
    """All distinct projected assignments, by blocking clauses (CryptoMiniSat).

    Returns (list of tuples of true projection variables, complete flag).
    """
    from pycryptosat import Solver
    solver = Solver(threads=1)
    solver.add_clauses(formula.clauses)
    found = []
    while limit is None or len(found) < limit:
        sat, model = solver.solve(time_limit=time_limit) if time_limit else solver.solve()
        if sat is None:
            return found, False
        if not sat:
            return found, True
        found.append(tuple(v for v in projection if model[v]))
        solver.add_clause([-v if model[v] else v for v in projection])
    return found, False


def approx_count(formula, projection, epsilon, delta, seed=1):
    """Hashing-based approximate projected model count (ApproxMC).

    Returns the estimate as a Python integer: cells * 2**hashes.
    """
    import pyapproxmc
    counter = pyapproxmc.Counter(seed=seed, epsilon=epsilon, delta=delta)
    counter.add_clauses(formula.clauses)
    # every variable must be known to the counter even if it occurs in no clause
    cells, hashes = counter.count(projection)
    return int(cells) * (1 << int(hashes))


def satisfiable(formula):
    from pycryptosat import Solver
    solver = Solver(threads=1)
    solver.add_clauses(formula.clauses)
    sat, _ = solver.solve()
    return bool(sat)
