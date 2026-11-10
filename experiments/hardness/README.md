# Brute-force checks of the SAT → CSS-distance reduction

These scripts test the direct reduction formalized in `lean/SatCosetWeight.lean`
(Step A), `lean/SatToDistance.lean` (Step B) and `lean/SatHardness.lean` (composition).
They are evidence only. The theorems are proved in Lean.

All scripts are plain Python 3 with no dependencies. Run them from this directory with
`python -I <script>`.

| Script | What it checks | Result (10 Nov 2026) |
|---|---|---|
| `reduction_check.py [seed]` | (a) Step A on 1,800 random CNFs (up to 5 variables, 10 clauses, width 3, some empty clauses): the minimum weight of a solution of `Hx = s` is `N + K` if the formula is satisfiable and `≥ N + K + 2` otherwise (no solution if there is an empty clause). The explicit kernel generators `P_i`, `D_{c,j}` lie in `ker H` and span it (rank check). (b) Step B on 1,492 random `(H, s)` with `s` in the column space and 1 to 3 copies `m, r`. The stabilizer distance, computed by enumerating `N \ S`, equals `min(1 + MLD(H,s), d_Z)`. (c) The full chain on 12 small satisfiable formulas (24 to 45 qubits), enumerating all supports of size `≤ t + 1`: there is an X-logical of weight exactly `t + 1`. | all passed (seed 1) |
| `unsat_chain.py <dir>` | The full chain on `x ∧ ¬x` in both clause orders (45 qubits). The lightest logical has weight `t + 2 = 5` (Z-type), so `d > t + 1 = 4`. | passed |
| `check_lean_rows.py lean_rows.txt` | An independent check of the check rows that the **Lean** function `reduce` computes, exported by `ExportRows.lean`. For each code it checks that the rows commute and that `k = 1`. It then tests the erasure criterion `2|E| − rank(S|E) − (rank S − rank(S|Eᶜ)) > 0` (the same formula as `PhysicalBridge/AmbiguityRank.lean`) on all `E` of size `thr`, and of size `thr + 1`. | `x₀` (24 qubits, thr 3): uncorrectable set of size 3 exists (satisfiable). `x₀ ∧ ¬x₀` (45 qubits, thr 4): none of size 4, one of size 5 (unsatisfiable, d = 5). `¬x₀ ∨ x₀` (45 qubits, thr 4): one of size 4 (satisfiable). All with k = 1. |

The construction differs slightly between the scripts and Lean. `reduction_check.py` uses an
appended block of `r` qubits linked by adjacent pairs `X_t X_{t+1}`. Lean (and therefore
`lean_rows.txt`) instead treats the appended coordinate like every other coordinate: it is
repeated `m + 1 = t + 2` times and linked to copy 0 by the star pairs `X_{(g,0)} X_{(g,k)}`.
Both generate the same stabilizer on the block (all even-weight X strings), so the codes
agree up to the choice of generators.

To regenerate `lean_rows.txt`, compile `ExportRows.lean` against the compiled module
`SatToDistance` (see `docs/BUILD.md`) and save its output.
