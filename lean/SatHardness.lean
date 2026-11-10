import SatToDistance

set_option autoImplicit false

/-!
# SAT reduces to approximating the erasure curve, and to one point estimate

Composition of the explicit reduction `reduce : Std.Sat.CNF Nat → Instance` (`SatToDistance`)
with the extraction theorems of `DistanceExtraction` (`cor_sparsehard_extraction`,
`cor_pointhard_extraction`, `cor_pointhard_extractionU`).

For every CNF `φ`, every rational `c > 1` and every map `A` from check matrices to outputs:
if `A` meets the paper's guarantee on the single sparse instance `sparsePad c (reduce φ).rows`,
then the computable post-processing (`distanceOfTable`, `distanceOfPoint`, `distanceOfPointU`)
of `A`'s output, compared with the threshold `(reduce φ).thr`, decides whether `φ` is
satisfiable. The instance has at most `c` nonzero entries per qubit on average.

These are the formal content of "SAT reduces (by a deterministic polynomial-size map) to the
relative approximation of the curve, and to a single point estimate". Polynomial *time* of
`reduce`, `sparsePad` and the extractions is evident from their definitions but is not
formalized; NP-hardness in the complexity-theoretic sense then follows from the Cook–Levin
theorem, which is not formalized here.
-/

namespace QecReliability.SatReduction

open scoped BigOperators
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.Padding QecReliability.DistanceDetermination
open QecPhysical.Stabilizer.Uncorrectable QecPhysical.Stabilizer.DistanceExtraction

/-- **SAT reduces to approximating the curve (`cor:sparsehard`).** -/
theorem sat_iff_table (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) {ε : ℝ} (hε : ε < 1)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) →
      Fin ((reduce φ).n + padM c (reduce φ).rows + 1) → ℚ)
    (hA : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve ((reduce φ).n + padM c (reduce φ).rows)
          (fun j => (A (sparsePad c (reduce φ).rows) j : ℝ)) p -
          infidelity (rowSpace (sparsePad c (reduce φ).rows)) p| ≤
        ε * infidelity (rowSpace (sparsePad c (reduce φ).rows)) p) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfTable (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a) ∧
      ((∃ a, φ.Sat a) → distanceOfTable (A (sparsePad c (reduce φ).rows)) = (reduce φ).thr) := by
  obtain ⟨d, hd⟩ := reduce_exists_isDistance φ
  obtain ⟨hsp, -, -, hdist⟩ := cor_sparsehard_extraction (reduce φ).rows hd c hc hε A hA
  refine ⟨hsp, ?_, fun hsat => ?_⟩
  · rw [hdist]; exact reduce_isDistance_le_iff φ hd
  · rw [hdist]; exact reduce_isDistance_eq φ hd hsat

/-- **SAT reduces to one point estimate of the infidelity (`cor:pointhard`).** -/
theorem sat_iff_point (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) → ℚ)
    (hA : infidelity (rowSpace (sparsePad c (reduce φ).rows))
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c (reduce φ).rows) ∧
        (A (sparsePad c (reduce φ).rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          infidelity (rowSpace (sparsePad c (reduce φ).rows))
            (pointAt ((reduce φ).n + padM c (reduce φ).rows) h)) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfPoint ((reduce φ).n + padM c (reduce φ).rows)
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) (2 ^ h)
          (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a) := by
  obtain ⟨d, hd⟩ := reduce_exists_isDistance φ
  obtain ⟨hsp, hdist⟩ :=
    cor_pointhard_extraction (reduce φ).rows (reduce_isotropic φ) hd c hc h A hA
  refine ⟨hsp, ?_⟩
  rw [hdist]
  exact reduce_isDistance_le_iff φ hd

/-- **SAT reduces to one point estimate of the uncorrectable probability.** -/
theorem sat_iff_pointU (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) → ℚ)
    (hA : uncorrectableProb (rowSpace (sparsePad c (reduce φ).rows))
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c (reduce φ).rows) ∧
        (A (sparsePad c (reduce φ).rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          uncorrectableProb (rowSpace (sparsePad c (reduce φ).rows))
            (pointAt ((reduce φ).n + padM c (reduce φ).rows) h)) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfPointU ((reduce φ).n + padM c (reduce φ).rows)
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) (2 ^ h)
          (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a) := by
  obtain ⟨d, hd⟩ := reduce_exists_isDistance φ
  obtain ⟨hsp, hdist⟩ :=
    cor_pointhard_extractionU (reduce φ).rows (reduce_isotropic φ) hd c hc h A hA
  refine ⟨hsp, ?_⟩
  rw [hdist]
  exact reduce_isDistance_le_iff φ hd

/-- The same in `Bool` form: the computable decision procedure built from `A` returns the truth
value of satisfiability. -/
theorem decide_table_eq (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) {ε : ℝ} (hε : ε < 1)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) →
      Fin ((reduce φ).n + padM c (reduce φ).rows + 1) → ℚ)
    (hA : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve ((reduce φ).n + padM c (reduce φ).rows)
          (fun j => (A (sparsePad c (reduce φ).rows) j : ℝ)) p -
          infidelity (rowSpace (sparsePad c (reduce φ).rows)) p| ≤
        ε * infidelity (rowSpace (sparsePad c (reduce φ).rows)) p) :
    (decide (distanceOfTable (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr) = true) ↔
      ∃ a, φ.Sat a := by
  rw [decide_eq_true_iff]
  exact (sat_iff_table φ c hc hε A hA).2.1

/-! ## Sanity checks on two tiny formulas -/

/-- `(x₀ ∨ x₁) ∧ ¬x₀`: satisfiable. -/
def phiSat : Std.Sat.CNF Nat := ⟨#[[(0, true), (1, true)], [(0, false)]]⟩

/-- `x₀ ∧ ¬x₀`: unsatisfiable. -/
def phiUnsat : Std.Sat.CNF Nat := ⟨#[[(0, true)], [(0, false)]]⟩

/-- The formula `[[]]` (one empty clause) is mapped to the same instance as `x₀ ∧ ¬x₀`. -/
def phiEmpty : Std.Sat.CNF Nat := ⟨#[[]]⟩

theorem phiSat_sat : phiSat.Sat (fun v => v == 1) := by
  rw [Std.Sat.CNF.sat_def]
  simp [phiSat, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

-- N = 2 variables, K = 3 occurrences: threshold 6, (2·2 + 3·3 + 1)(2 + 3 + 2) = 98 qubits.
example : (reduce phiSat).thr = 6 ∧ (reduce phiSat).n = 98 := by decide
-- N = 1, K = 2: threshold 4, (2 + 6 + 1)(1 + 2 + 2) = 45 qubits.
example : (reduce phiUnsat).thr = 4 ∧ (reduce phiUnsat).n = 45 := by decide
example : (reduce phiEmpty).thr = 4 ∧ (reduce phiEmpty).n = 45 := by decide

theorem phiSat_distance {d : ℕ} (hd : IsDistance (rowSpace (reduce phiSat).rows) d) : d = 6 :=
  reduce_isDistance_eq phiSat hd ⟨_, phiSat_sat⟩

theorem phiUnsat_not_sat : ¬ ∃ a, phiUnsat.Sat a := by
  rintro ⟨a, ha⟩
  revert ha
  unfold phiUnsat
  rw [Std.Sat.CNF.sat_def]
  cases h : a 0 <;> simp [Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval, h]

theorem phiUnsat_distance {d : ℕ} (hd : IsDistance (rowSpace (reduce phiUnsat).rows) d) :
    4 < d := by
  have := (reduce_isDistance_le_iff phiUnsat hd).not.2 phiUnsat_not_sat
  have h4 : (reduce phiUnsat).thr = 4 := by decide
  omega

end QecReliability.SatReduction

#print axioms QecReliability.SatReduction.sat_iff_table
#print axioms QecReliability.SatReduction.sat_iff_point
#print axioms QecReliability.SatReduction.sat_iff_pointU
#print axioms QecReliability.SatReduction.decide_table_eq
#print axioms QecReliability.SatReduction.phiSat_distance
#print axioms QecReliability.SatReduction.phiUnsat_distance
