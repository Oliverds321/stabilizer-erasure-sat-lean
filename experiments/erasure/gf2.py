"""GF(2) linear algebra: small dense helpers and a bit-packed, numba-compiled
routine for the erasure exponent

    d_E = dim N_E - dim S_E = 2|E| - rank(H_E) - s + rank(H_{E^c}),

where H_E keeps both columns (X and Z) of every qubit in E and s = rank(H).
"""
import numpy as np
from numba import njit, prange

WORD = 64


def rank_dense(mat):
    mat = (np.array(mat, dtype=np.uint8) % 2).copy()
    if mat.size == 0:
        return 0
    rows, cols = mat.shape
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if mat[i, c]:
                piv = i
                break
        if piv is None:
            continue
        mat[[r, piv]] = mat[[piv, r]]
        for i in range(rows):
            if i != r and mat[i, c]:
                mat[i] ^= mat[r]
        r += 1
        if r == rows:
            break
    return r


def nullspace_dense(mat):
    """Basis (rows) of {v : mat v = 0} over GF(2)."""
    mat = (np.array(mat, dtype=np.uint8) % 2).copy()
    rows, cols = mat.shape
    pivots = []
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if mat[i, c]:
                piv = i
                break
        if piv is None:
            continue
        mat[[r, piv]] = mat[[piv, r]]
        for i in range(rows):
            if i != r and mat[i, c]:
                mat[i] ^= mat[r]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = np.zeros((len(free), cols), dtype=np.uint8)
    for idx, f in enumerate(free):
        basis[idx, f] = 1
        for row, p in enumerate(pivots):
            if mat[row, f]:
                basis[idx, p] = 1
    return basis


def pack_rows(mat):
    """Pack an m x c 0/1 matrix into m x ceil(c/64) uint64 words."""
    mat = np.array(mat, dtype=np.uint8) % 2
    m, c = mat.shape
    words = (c + WORD - 1) // WORD
    out = np.zeros((m, words), dtype=np.uint64)
    for j in range(c):
        col = mat[:, j].astype(np.uint64)
        out[:, j // WORD] |= col << np.uint64(j % WORD)
    return out


@njit(cache=True)
def _rank_masked(rows, mask, work):
    """Rank of the rows restricted to the columns selected by `mask`."""
    m, words = rows.shape
    for i in range(m):
        for w in range(words):
            work[i, w] = rows[i, w] & mask[w]
    rank = 0
    for w in range(words):
        bits = mask[w]
        while bits != 0:
            low = bits & (~bits + np.uint64(1))
            bits ^= low
            piv = -1
            for i in range(rank, m):
                if work[i, w] & low:
                    piv = i
                    break
            if piv < 0:
                continue
            if piv != rank:
                for ww in range(words):
                    tmp = work[rank, ww]
                    work[rank, ww] = work[piv, ww]
                    work[piv, ww] = tmp
            for i in range(rank + 1, m):
                if work[i, w] & low:
                    for ww in range(w, words):
                        work[i, ww] ^= work[rank, ww]
            rank += 1
            if rank == m:
                return rank
    return rank


@njit(cache=True)
def _qubit_mask(erased, n, words, mask):
    """mask <- both columns (i and n+i) of every qubit with erased[i] != 0."""
    for w in range(words):
        mask[w] = 0
    for i in range(n):
        if erased[i]:
            mask[i // 64] |= np.uint64(1) << np.uint64(i % 64)
            j = n + i
            mask[j // 64] |= np.uint64(1) << np.uint64(j % 64)


@njit(cache=True)
def exponent(rows, n, s, erased, mask, full, work):
    """d_E for the 0/1 vector `erased`; `full` is the all-columns mask."""
    words = rows.shape[1]
    _qubit_mask(erased, n, words, mask)
    size = 0
    for i in range(n):
        if erased[i]:
            size += 1
    r_in = _rank_masked(rows, mask, work)
    for w in range(words):
        mask[w] = full[w] & ~mask[w]
    r_out = _rank_masked(rows, mask, work)
    return 2 * size - r_in - s + r_out


def full_mask(n):
    words = (2 * n + WORD - 1) // WORD
    full = np.zeros(words, dtype=np.uint64)
    for j in range(2 * n):
        full[j // WORD] |= np.uint64(1) << np.uint64(j % WORD)
    return full


def exponent_of(code, erased_set):
    rows = pack_rows(code.h)
    n = code.n
    erased = np.zeros(n, dtype=np.uint8)
    erased[list(erased_set)] = 1
    return int(exponent(rows, n, code.s, erased, np.zeros(rows.shape[1], np.uint64),
                        full_mask(n), np.zeros_like(rows)))


@njit(parallel=True, cache=True)
def _enumerate_all(rows, n, s, full, maxd, threads):
    """Histogram hist[j, d] = #{E : |E| = j, d_E = d} over all 2^n sets."""
    total = np.int64(1) << np.int64(n)
    hist = np.zeros((threads, n + 1, maxd + 1), dtype=np.int64)
    chunk = total // threads + 1
    for t in prange(threads):
        mask = np.zeros(rows.shape[1], dtype=np.uint64)
        work = np.zeros_like(rows)
        erased = np.zeros(n, dtype=np.uint8)
        lo = t * chunk
        hi = min(total, lo + chunk)
        for e in range(lo, hi):
            size = 0
            for i in range(n):
                bit = (e >> i) & 1
                erased[i] = bit
                size += bit
            d = exponent(rows, n, s, erased, mask, full, work)
            hist[t, size, d] += 1
    return hist.sum(axis=0)


def enumerate_all(code, threads=8):
    """Exact histogram of (|E|, d_E) by exhaustive enumeration (n <= ~28)."""
    rows = pack_rows(code.h)
    return _enumerate_all(rows, code.n, code.s, full_mask(code.n), 2 * code.k, threads)


@njit(parallel=True, cache=True)
def _sample_layer(rows, n, s, full, maxd, j, samples, threads, seed):
    hist = np.zeros((threads, maxd + 1), dtype=np.int64)
    per = samples // threads
    for t in prange(threads):
        np.random.seed(seed + 7919 * t + 104729 * j)
        mask = np.zeros(rows.shape[1], dtype=np.uint64)
        work = np.zeros_like(rows)
        erased = np.zeros(n, dtype=np.uint8)
        perm = np.arange(n)
        for _ in range(per):
            for i in range(n):
                erased[i] = 0
            for i in range(j):  # partial Fisher-Yates: uniform j-subset
                r = i + np.random.randint(0, n - i)
                tmp = perm[i]
                perm[i] = perm[r]
                perm[r] = tmp
                erased[perm[i]] = 1
            d = exponent(rows, n, s, erased, mask, full, work)
            hist[t, d] += 1
    return hist.sum(axis=0)


def sample_layer(code, j, samples, threads=8, seed=1):
    """Histogram over d_E for `samples` uniform erased sets of size j."""
    rows = pack_rows(code.h)
    return _sample_layer(rows, code.n, code.s, full_mask(code.n), 2 * code.k, j,
                         samples, threads, seed)
