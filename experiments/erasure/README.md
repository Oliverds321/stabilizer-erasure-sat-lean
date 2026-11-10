# Computed examples for the erasure-reliability paper

Code behind the "Computed examples" section of
`paper/quantum-erasure-reliability/manuscript.tex`. Python 3.11 with `numpy`,
`numba`, `matplotlib`, `python-sat`, `pycryptosat` and `pyapproxmc`
(`pip install python-sat pycryptosat pyapproxmc`).

| File | What it does |
|---|---|
| `qec_codes.py` | Check matrices: five-qubit, Steane, Shor, rotated surface, toric, Hamming CSS, bivariate bicycle. `python qec_codes.py` lists them. |
| `gf2.py` | Bit-packed GF(2) ranks; `d_E = 2|E| - rank(H_E) - s + rank(H_{E^c})`; exhaustive enumeration over all `2^n` erased sets; uniform sampling of a layer. |
| `certificates.py` | The Good/Bad certificates of the paper as explicit 3-CNF (XOR chains, Tseitin gates, totalizer); blocking-clause enumeration; ApproxMC interface. |
| `test_small.py` | Checks that the projected model counts of the 3-CNFs equal the exact `A_j`, `B_j` and uncorrectable-set counts on small codes. |
| `paper_algorithm.py` | The algorithm of the main theorem with ApproxMC + CryptoMiniSat in place of the linear-size hash and the subexponential engine. |
| `hybrid.py` | Practical estimator: SAT enumeration of all minimal uncorrectable sets up to a size `w` (complete level by level, cached in `results/minimal_CODE.json`; for toric and BB codes the search uses verified translation symmetries, one orbit representative per parallel process), Karp-Luby union sampling for layers `j <= w`, the dual for layers `n - j <= w`, uniform sampling in between, and for layers just above `w` where plain sampling sees too few events the split estimator (listed union + sampled remainder). |
| `validate_hybrid.py` | z-scores of every hybrid layer estimate against exhaustive enumeration; also checks the duality `d_E + d_{E^c} = 2k`. |
| `test_symmetry.py` | Checks that the symmetry-reduced parallel enumeration returns exactly the list of the plain enumeration (toric3 through size 6, toric4 through 10, bb72 through 11; surface5 has a trivial group). |
| `analyze.py` | Reads `results/`, writes `results/summary.json`, the LaTeX tables and the figures in `paper/.../figures/`. |
| `observations.py` | Prints the numbers quoted in the section's prose (leading coefficients, ratios to the leading term, split-layer statistics). |
| `certify.py` | Proof-checked completeness of the lists of minimal uncorrectable sets: the statement "an uncorrectable set of size <= L contains no listed set" is refuted by CaDiCaL with an LRAT proof, checked by the verified LRAT checker of Lean core. With `--lean` the formula is `certFormula` of `lean/CompletenessFormula.lean`, built and checked by `tools/lrat/CertifyList.lean` (meaning proved in Lean); without it the formula is written by Python and checked by `tools/lrat/CheckLrat.lean`. `--symmetric` uses orbit representatives, `--split-depth` splits instances whose proofs are too large. Results: `results/certified_lean_CODE.json`, `results/certified_CODE.json`. |
| `certify_lean.py` | Single-instance driver for the Lean-defined formula (emit, CaDiCaL, check), with a negative test (`--drop`) and a comparison with the Python formula (`--compare`). |
| `certify_code.py` | One Lean-checked certificate per code: writes a bundle (check rows, listed sets with uncorrectability witnesses, symmetry generators and image tables, case-split leaves), runs `tools/lrat/CertifyCode.lean`, whose checks are proved sound in `lean/ListCertificate.lean`, and stores `results/certificate_CODE.json` (level reached, distance, number of minimum-size sets). Has negative tests (`--neg`). |
| `curves.py` | Exact coefficient tables `f_j`, `u_j` by exhaustive enumeration (`results/exact_CODE.json`) and evaluation of the curves. |
| `exact_lean.py` | Recomputes the exhaustive tables with the Lean function of `lean/ExactTable.lean` (proved equal to the definitions) through `tools/exact/ExactTable.lean` and compares them entry by entry, as exact fractions, with the Python tables; writes `results/exact_lean_CODE.json`. Done for the seven codes of at most 25 qubits (the 25-qubit table takes about three hours). |
| `ashikhmin_example.py` | External check against a published table: recomputes the 17 nonzero invariants and the numbers of unrecoverable sets of the [[12,6]] code of Example 1 of Ashikhmin (ISIT 2020) by a standalone enumeration and by the pipeline's enumerator, and writes `results/ashikhmin_example.json` and `results/exact_ashikhmin12.json`; `python exact_lean.py ashikhmin12` then compares the verified Lean table with it. |
| `pipeline_figure.py` | Figure 1 of the manuscript. |
| `bench_approxmc.py` | Timing probe for single layers. |

Typical commands:

    python -u test_small.py
    python -u paper_algorithm.py surface5 0.3 --workers 6
    python -u validate_hybrid.py surface5 8
    python -u test_symmetry.py
    python -u hybrid.py bb72 11 --threads 12
    SAT_THREADS=6 python -u hybrid.py bb90 13 --threads 14 --sat-time 5400
    python analyze.py

Results of the runs reported in the paper are in `results/` (JSON).
`results/minimal_CODE.json` are the complete lists of minimal uncorrectable sets and
`results/validation_CODE_wW_sN.json` the checks against exhaustive enumeration. The time
recorded by `paper_algorithm.py` is wall-clock time per count (one single-threaded process each).

The scripts that call Lean (`certify.py --lean`, `certify_lean.py`, `certify_code.py`,
`exact_lean.py`) expect the Lean 4.34.1 toolchain and the compiled modules of this
development in a sibling directory `local-build/` of the repository; the paths are
set at the top of each script.

What is and is not guaranteed:

- `paper_algorithm.py` carries the (eps, delta) guarantee of ApproxMC for each
  count, hence the two-tail guarantee of the theorem, assuming the SAT solver
  is correct. Its dense XOR hashes are not the linear-size hash of the paper.
- `hybrid.py`: levels reported "complete" rest on UNSAT answers of the SAT
  solver. Layer estimates are unbiased with the reported standard errors
  (central limit theorem); they are statistical, not worst-case, statements.
  The symmetry reduction and the identities used (duality, union identity and
  its split form, minimal-set criterion) are proved in `lean/HybridEstimator.lean`
  and `lean/HybridSymmetry.lean`; `hybrid.symmetry_group` checks by a rank
  computation that every permutation it uses preserves the row space.
  `SAT_THREADS` sets the number of CryptoMiniSat threads per search (default 1).
- Exhaustive enumeration is exact rational arithmetic and is the reference.
