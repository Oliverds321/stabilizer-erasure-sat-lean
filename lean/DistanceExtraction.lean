import DistanceWeight
import DistanceDetermination
import PaddingInvariance
import HybridEstimator

set_option autoImplicit false

/-!
# The hardness reductions as computable functions

X1. `distanceOfTable c` (first nonzero entry of a rational coefficient table) recovers the
    distance from any table whose Bernstein curve is within relative error `ε < 1` of the
    optimal infidelity (curve form, coefficient form and channel form).
X2. `distanceOfPoint n p R est` (least `d' ≤ n` passing the numeric test of
    `infidelity_point_determines_distance`) recovers the distance from one point estimate within
    factor `R`; `distanceOfPointU` does the same for the uncorrectable probability.
X3. Padding: `padRows m rows` has the same distance, the same `I(p)` and `U(p)`, and
    `rowIncidences rows + m` nonzero entries; `padCount c n w = ⌈(w - c n)/(c - 1)⌉₊` makes it
    `c`-sparse for any rational `c > 1`.
X4. Summary theorems for `cor:sparsehard` and `cor:pointhard`: extraction applied to any valid
    output on the padded instance returns the distance of the original code.

The remaining step to NP-hardness is the cited theorem that the minimum distance of a
stabilizer code is NP-hard (Kapshikar–Kundu 2023); together with `isDistance_iff_minWeight`
(`IsDistance` is the minimum logical weight) this file reduces that problem to the
approximation problems. Polynomial-time computability of `padRows`, `padCount`,
`distanceOfTable` and `distanceOfPoint` is evident from their definitions (a list append,
a ceiling, and a scan of at most `n + 1` rational tests) but is not formalized; no complexity
classes appear here.
-/

namespace QecPhysical.Stabilizer.DistanceExtraction

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.Padding
open QecReliability.DistanceDetermination
open QecPhysical.Stabilizer.Uncorrectable

/-! ## A computable first-true search -/

/-- `firstTrue f k` is the least `i < k` with `f i = true`, or `k` if there is none. -/
def firstTrue (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if firstTrue f k < k then firstTrue f k else if f k then k else k + 1

theorem firstTrue_of_none (f : ℕ → Bool) :
    ∀ k, (∀ i < k, f i = false) → firstTrue f k = k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have hk : firstTrue f k = k := ih (fun i hi => h i (by omega))
    simp [firstTrue, hk, h k (by omega)]

theorem firstTrue_eq (f : ℕ → Bool) {d : ℕ} (hd : f d = true) (hlt : ∀ i < d, f i = false) :
    ∀ k, d < k → firstTrue f k = d := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    by_cases hdk : d < k
    · have := ih hdk
      simp [firstTrue, this, hdk]
    · have hdk' : d = k := by omega
      subst hdk'
      have h0 : firstTrue f d = d := firstTrue_of_none f d hlt
      simp [firstTrue, h0, hd]

theorem firstTrue_unique (f : ℕ → Bool) {d k : ℕ} (h : ∀ d', f d' = true ↔ d' = d)
    (hdk : d < k) : firstTrue f k = d :=
  firstTrue_eq f ((h d).mpr rfl) (fun i hi => by
    cases hfi : f i
    · rfl
    · exact absurd ((h i).mp hfi) (by omega)) k hdk

/-! ## X1. Distance from a coefficient table -/

/-- Index of the first nonzero entry of a rational table (`n + 1` if all entries vanish). -/
def distanceOfTable {n : ℕ} (c : Fin (n + 1) → ℚ) : ℕ :=
  firstTrue (fun i => if h : i < n + 1 then decide (c ⟨i, h⟩ ≠ 0) else false) (n + 1)

theorem distanceOfTable_eq_of {n : ℕ} {c : Fin (n + 1) → ℚ} {d : ℕ} (hd : d < n + 1)
    (hcd : c ⟨d, hd⟩ ≠ 0) (hbelow : ∀ i : Fin (n + 1), i.val < d → c i = 0) :
    distanceOfTable c = d := by
  unfold distanceOfTable
  refine firstTrue_eq _ ?_ ?_ (n + 1) hd
  · simp [hd, hcd]
  · intro i hi
    have hin : i < n + 1 := by omega
    simp [hin, hbelow ⟨i, hin⟩ hi]

/-- Sanity check: the functions evaluate. -/
example : distanceOfTable (n := 3) ![0, 0, 3, 1] = 2 := by decide
example : distanceOfTable (n := 2) ![0, 0, 0] = 3 := by decide

variable {n : ℕ}

/-- The true infidelity coefficients `1 - (average of 2^{-d_E} over |E| = j)`. -/
noncomputable def trueCoeff (S : Submodule Bit (Pauli n)) (j : Fin (n + 1)) : ℝ :=
  1 - layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S) j

theorem erasureScore_eq_one_iff (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    erasureScore S E = 1 ↔ ambiguity (symplectic n) S (supported E) = 0 := by
  unfold erasureScore
  exact EnumeratorExample.inv_two_pow_eq_one_iff _

theorem trueCoeff_eq_zero_iff (S : Submodule Bit (Pauli n)) (j : Fin (n + 1)) :
    trueCoeff S j = 0 ↔
      ∀ E : Finset (Fin n), E.card = j.val → ambiguity (symplectic n) S (supported E) = 0 := by
  unfold trueCoeff
  rw [sub_eq_zero, eq_comm,
    layerAverage_eq_one_iff (id : Causes n → Finset (Fin n)) (erasureScore S)
      (erasureScore_le_one S) j]
  constructor
  · intro h E hE
    exact (erasureScore_eq_one_iff S E).mp (h E (Fin.ext hE))
  · intro h E hE
    exact (erasureScore_eq_one_iff S E).mpr (h E (congrArg Fin.val hE))

theorem trueCoeff_nonneg (S : Submodule Bit (Pauli n)) (j : Fin (n + 1)) : 0 ≤ trueCoeff S j :=
  sub_nonneg.mpr (layerAverage_range _ (erasureScore S)
    (fun E => ⟨by unfold erasureScore; positivity, erasureScore_le_one S E⟩) j).2

theorem infidelity_eq_trueCurve (S : Submodule Bit (Pauli n)) (p : ℝ) :
    infidelity S p = bernsteinCurve n (trueCoeff S) p := by
  rw [infidelity_eq]
  exact (bernsteinCurve_complement n _ p).symm

theorem isDistance_le (S : Submodule Bit (Pauli n)) {d : ℕ} (hd : IsDistance S d) : d ≤ n := by
  obtain ⟨E, hE, _⟩ := hd.2
  have := E.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-- **X1 (curve form).** Any rational table whose Bernstein curve is within relative error
`ε < 1` of `I(p)` on `(0,1]` has its first nonzero entry exactly at the distance. -/
theorem distanceOfTable_correct (S : Submodule Bit (Pauli n)) {d : ℕ} (hd : IsDistance S d)
    (c : Fin (n + 1) → ℚ) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n (fun j => (c j : ℝ)) p - infidelity S p| ≤ ε * infidelity S p) :
    distanceOfTable c = d := by
  obtain ⟨E0, hE0c, hE0⟩ := hd.2
  have hdn : d < n + 1 := by have := isDistance_le S hd; omega
  set j : Fin (n + 1) := ⟨d, hdn⟩
  have hb : trueCoeff S j ≠ 0 ∧ ∀ i < j, trueCoeff S i = 0 := by
    constructor
    · intro h0
      have := (trueCoeff_eq_zero_iff S j).1 h0 E0 hE0c
      omega
    · intro i hi
      rw [trueCoeff_eq_zero_iff]
      intro E hE
      by_contra hne
      exact hd.1 E (by rw [hE]; exact hi) (Nat.pos_of_ne_zero hne)
  have h' : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n (fun j => (c j : ℝ)) p - bernsteinCurve n (trueCoeff S) p| ≤
        ε * bernsteinCurve n (trueCoeff S) p := by
    intro p hp
    rw [← infidelity_eq_trueCurve]
    exact h p hp
  have key := (first_nonzero_iff (trueCoeff S) (fun j => (c j : ℝ)) (trueCoeff_nonneg S) hε h'
    j).2 hb
  apply distanceOfTable_eq_of hdn
  · have := key.1
    exact_mod_cast this
  · intro i hi
    have := key.2 i (Fin.lt_iff_val_lt_val.mpr hi)
    exact_mod_cast this

/-- **X1 (coefficient form).** The two-sided coefficientwise bound
`|c_j - b_j| ≤ ε b_j` against the true coefficients suffices. -/
theorem distanceOfTable_correct_coeff (S : Submodule Bit (Pauli n)) {d : ℕ}
    (hd : IsDistance S d) (c : Fin (n + 1) → ℚ) {ε : ℝ} (hε : ε < 1)
    (hc : ∀ j, |(c j : ℝ) - trueCoeff S j| ≤ ε * trueCoeff S j) :
    distanceOfTable c = d :=
  distanceOfTable_correct S hd c hε (fun p hp => by
    rw [infidelity_eq_trueCurve]
    exact bernsteinCurve_rel_of_coeff hc hp.1.le hp.2)

/-- **X1 (channel form).** The guarantee stated against the optimal physical infidelity
`1 - F(p)` of the iid flagged erasure channel. -/
theorem distanceOfTable_correct_channel {S : Submodule Bit (Pauli n)} (L : Lift S) {d : ℕ}
    (hd : IsDistance S d) (c : Fin (n + 1) → ℚ) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p (hp : p ∈ Set.Icc (0 : ℝ) 1),
      |bernsteinCurve n (fun j => (c j : ℝ)) p - (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map)| ≤
        ε * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map)) :
    distanceOfTable c = d :=
  distanceOfTable_correct S hd c hε (fun p hp => by
    have hp' : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2⟩
    have := h p hp'
    rw [← infidelity_eq_channel L p hp'.1 hp'.2] at this
    exact this)

/-! ## X2. Distance from one point estimate -/

/-- The numeric test of `infidelity_point_determines_distance`. -/
def pointTest (n : ℕ) (p R est : ℚ) (d' : ℕ) : Bool :=
  decide (p ^ d' / (2 * R) ≤ est ∧ est ≤ 2 ^ n * R * p ^ d')

/-- The numeric test of `uncorrectableProb_point_determines_distance`. -/
def pointTestU (n : ℕ) (p R est : ℚ) (d' : ℕ) : Bool :=
  decide (p ^ d' / R ≤ est ∧ est ≤ 2 ^ n * R * p ^ d')

/-- Least `d' ≤ n` passing the test (`n + 1` if none). -/
def distanceOfPoint (n : ℕ) (p R est : ℚ) : ℕ := firstTrue (pointTest n p R est) (n + 1)

def distanceOfPointU (n : ℕ) (p R est : ℚ) : ℕ := firstTrue (pointTestU n p R est) (n + 1)

/-- **X2.** Under the hypotheses of `infidelity_point_determines_distance` (with rational
`p, R, est`), the extracted value is the distance. -/
theorem distanceOfPoint_correct (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℚ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : 2 ^ (n + 1) * R ^ 2 * p < 1)
    (hest : infidelity S p / R ≤ est ∧ (est : ℝ) ≤ R * infidelity S p) :
    distanceOfPoint n p R est = d := by
  have hthm := infidelity_point_determines_distance S hS hd (p := (p : ℝ)) (R := (R : ℝ))
    (est := (est : ℝ)) (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by exact_mod_cast hR)
    (by exact_mod_cast hsmall) hest
  refine firstTrue_unique _ (fun d' => ?_) (by have := isDistance_le S hd; omega)
  rw [← hthm d']
  unfold pointTest
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    · have := (Rat.cast_le (K := ℝ)).mpr h2
      push_cast at this
      exact this
  · rintro ⟨h1, h2⟩
    constructor
    · have : ((p ^ d' / (2 * R) : ℚ) : ℝ) ≤ (est : ℝ) := by push_cast; exact h1
      exact_mod_cast this
    · have : (est : ℝ) ≤ ((2 ^ n * R * p ^ d' : ℚ) : ℝ) := by push_cast; exact h2
      exact_mod_cast this

/-- **X2 (uncorrectable probability).** -/
theorem distanceOfPointU_correct (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℚ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : 2 ^ n * R ^ 2 * p < 1)
    (hest : uncorrectableProb S p / R ≤ est ∧ (est : ℝ) ≤ R * uncorrectableProb S p) :
    distanceOfPointU n p R est = d := by
  have hthm := uncorrectableProb_point_determines_distance S hS hd (p := (p : ℝ)) (R := (R : ℝ))
    (est := (est : ℝ)) (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by exact_mod_cast hR)
    (by exact_mod_cast hsmall) hest
  refine firstTrue_unique _ (fun d' => ?_) (by have := isDistance_le S hd; omega)
  rw [← hthm d']
  unfold pointTestU
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    · have := (Rat.cast_le (K := ℝ)).mpr h2
      push_cast at this
      exact this
  · rintro ⟨h1, h2⟩
    constructor
    · have : ((p ^ d' / R : ℚ) : ℝ) ≤ (est : ℝ) := by push_cast; exact h1
      exact_mod_cast this
    · have : (est : ℝ) ≤ ((2 ^ n * R * p ^ d' : ℚ) : ℝ) := by push_cast; exact h2
      exact_mod_cast this

/-! ## X3. Padding -/

variable {m : ℕ}

/-- Original erased sets inside the padded register. -/
def liftSet (m : ℕ) (E : Finset (Fin n)) : Finset (Fin (n + m)) :=
  E.map ⟨Fin.castAdd m, Fin.castAdd_injective n m⟩

theorem oldSet_liftSet (E : Finset (Fin n)) : oldSet m (liftSet m E) = E := by
  ext i
  simp [liftSet]

theorem card_liftSet (E : Finset (Fin n)) : (liftSet m E).card = E.card := Finset.card_map _

theorem card_oldSet_le (E' : Finset (Fin (n + m))) : (oldSet m E').card ≤ E'.card := by
  rw [card_split E']
  omega

/-- Padding preserves the distance. -/
theorem isDistance_pad (S : Submodule Bit (Pauli n)) (d : ℕ) :
    IsDistance (pad m S) d ↔ IsDistance S d := by
  constructor
  · intro hd
    have h1 : ∀ E : Finset (Fin n), E.card < d →
        ¬ 0 < ambiguity (symplectic n) S (supported E) := by
      intro E hE hpos
      apply hd.1 (liftSet m E) (by rw [card_liftSet]; exact hE)
      rw [ambiguity_pad, oldSet_liftSet]
      exact hpos
    refine ⟨h1, ?_⟩
    obtain ⟨E', hE', hpos⟩ := hd.2
    rw [ambiguity_pad] at hpos
    refine ⟨oldSet m E', ?_, hpos⟩
    have hle := card_oldSet_le (m := m) E'
    by_contra hne
    exact h1 _ (by omega) hpos
  · intro hd
    refine ⟨fun E' hE' hpos => ?_, ?_⟩
    · rw [ambiguity_pad] at hpos
      exact hd.1 _ (lt_of_le_of_lt (card_oldSet_le E') hE') hpos
    · obtain ⟨E, hE, hpos⟩ := hd.2
      refine ⟨liftSet m E, by rw [card_liftSet, hE], ?_⟩
      rw [ambiguity_pad, oldSet_liftSet]
      exact hpos

theorem infidelity_pad (S : Submodule Bit (Pauli n)) (p : ℝ) :
    infidelity (pad m S) p = infidelity S p := by
  unfold infidelity infidelityScore
  simp only [erasureScore_pad]
  exact causeMass_sum_pad p (fun E => 1 - erasureScore S E)

theorem uncorrectableProb_pad (S : Submodule Bit (Pauli n)) (p : ℝ) :
    uncorrectableProb (pad m S) p = uncorrectableProb S p := by
  unfold uncorrectableProb uncorrectable
  simp only [ambiguity_pad]
  exact causeMass_sum_pad p (fun E => if 0 < ambiguity (symplectic n) S (supported E) then 1 else 0)

/-- Row-level padding preserves the distance. -/
theorem isDistance_padRows (rows : List (List (PauliCoord n))) (d : ℕ) :
    IsDistance (rowSpace (padRows m rows)) d ↔ IsDistance (rowSpace rows) d := by
  rw [rowSpace_padRows]
  exact isDistance_pad _ d

theorem isotropic_padRows (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) :
    rowSpace (padRows m rows) ≤ normalizer (symplectic (n + m)) (rowSpace (padRows m rows)) := by
  rw [rowSpace_padRows]
  exact pad_isotropic hS

/-- Number of padding qubits for target sparsity `c`: `⌈(w - c n)/(c - 1)⌉₊`. -/
def padCount (c : ℚ) (n w : ℕ) : ℕ := ⌈((w : ℚ) - c * n) / (c - 1)⌉₊

/-- The padding count used for `rows`. -/
def padM (c : ℚ) (rows : List (List (PauliCoord n))) : ℕ := padCount c n (rowIncidences rows)

/-- The sparse instance: `rows` padded by `padM c rows` single-`Z` rows. -/
def sparsePad (c : ℚ) (rows : List (List (PauliCoord n))) :
    List (List (PauliCoord (n + padM c rows))) :=
  padRows (padM c rows) rows

/-- **X3 (sparsity).** For rational `c > 1`, the padded instance has at most `c · (n + m)`
nonzero entries. -/
theorem sparsePad_sparse (c : ℚ) (hc : 1 < c) (rows : List (List (PauliCoord n))) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) := by
  unfold sparsePad
  rw [rowIncidences_padRows]
  set w := rowIncidences rows
  set k := padM c rows
  have hceil : ((w : ℚ) - c * n) / (c - 1) ≤ k := Nat.le_ceil _
  have hc1 : 0 < c - 1 := by linarith
  rw [div_le_iff₀ hc1] at hceil
  push_cast
  nlinarith

theorem rowIncidences_sparsePad (c : ℚ) (rows : List (List (PauliCoord n))) :
    rowIncidences (sparsePad c rows) = rowIncidences rows + padM c rows :=
  rowIncidences_padRows rows

/-! ## X4. Summary theorems for the two corollaries -/

/-- **cor:sparsehard, composed.** For any rows with distance `d` and any rational `c > 1`:
the sparse instance `sparsePad c rows` has at most `c · n'` nonzero entries, and for any
output table `A (sparsePad c rows)` whose Bernstein curve is within relative error `ε < 1` of
the infidelity of the sparse instance on `(0,1]`, `distanceOfTable` returns `d`. -/
theorem cor_sparsehard_extraction (rows : List (List (PauliCoord n))) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) {ε : ℝ} (hε : ε < 1)
    (A : List (List (PauliCoord (n + padM c rows))) → Fin (n + padM c rows + 1) → ℚ)
    (hA : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve (n + padM c rows) (fun j => (A (sparsePad c rows) j : ℝ)) p -
          infidelity (rowSpace (sparsePad c rows)) p| ≤
        ε * infidelity (rowSpace (sparsePad c rows)) p) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      IsDistance (rowSpace (sparsePad c rows)) d ∧
      (∀ p : ℝ, infidelity (rowSpace (sparsePad c rows)) p = infidelity (rowSpace rows) p) ∧
      distanceOfTable (A (sparsePad c rows)) = d := by
  have hd' : IsDistance (rowSpace (sparsePad c rows)) d := (isDistance_padRows rows d).mpr hd
  refine ⟨sparsePad_sparse c hc rows, hd', fun p => ?_,
    distanceOfTable_correct _ hd' _ hε hA⟩
  unfold sparsePad
  rw [rowSpace_padRows]
  exact infidelity_pad _ p

/-- The point of `cor:pointhard`: `p_N = 2^{-(N + 2h + 2)}`. -/
def pointAt (N h : ℕ) : ℚ := (1 / 2) ^ (N + 2 * h + 2)

theorem pointAt_small (N h : ℕ) : 2 ^ (N + 1) * ((2 : ℚ) ^ h) ^ 2 * pointAt N h = 1 / 2 := by
  unfold pointAt
  rw [one_div_pow, ← pow_mul, ← pow_add, show N + 2 * h + 2 = (N + 1 + h * 2) + 1 by ring,
    pow_succ]
  have : (0 : ℚ) < 2 ^ (N + 1 + h * 2) := by positivity
  field_simp

theorem pointAt_pos (N h : ℕ) : 0 < pointAt N h := by unfold pointAt; positivity

theorem pointAt_le_one (N h : ℕ) : pointAt N h ≤ 1 := by
  unfold pointAt
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **cor:pointhard, composed (infidelity).** For isotropic rows with distance `d`, `c > 1`
and `h : ℕ`, with `N = n + padM c rows`, `p = p_N`, `R = 2^h`: any rational output
`A (sparsePad c rows)` within factor `R` of `I(p)` of the sparse instance makes
`distanceOfPoint N p R` return `d`. -/
theorem cor_pointhard_extraction (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord (n + padM c rows))) → ℚ)
    (hA : infidelity (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c rows) ∧
        (A (sparsePad c rows) : ℝ) ≤
          ((2 : ℚ) ^ h : ℚ) * infidelity (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h)) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      distanceOfPoint (n + padM c rows) (pointAt (n + padM c rows) h) (2 ^ h)
        (A (sparsePad c rows)) = d := by
  have hd' : IsDistance (rowSpace (sparsePad c rows)) d := (isDistance_padRows rows d).mpr hd
  have hS' := isotropic_padRows (m := padM c rows) rows hS
  refine ⟨sparsePad_sparse c hc rows, ?_⟩
  refine distanceOfPoint_correct _ hS' hd' (pointAt_pos _ h) (pointAt_le_one _ h)
    (one_le_pow₀ (by norm_num)) ?_ hA
  rw [pointAt_small]
  norm_num

/-- **cor:pointhard, composed (uncorrectable probability).** -/
theorem cor_pointhard_extractionU (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord (n + padM c rows))) → ℚ)
    (hA : uncorrectableProb (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h) /
          ((2 : ℚ) ^ h : ℚ) ≤ A (sparsePad c rows) ∧
        (A (sparsePad c rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          uncorrectableProb (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h)) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      distanceOfPointU (n + padM c rows) (pointAt (n + padM c rows) h) (2 ^ h)
        (A (sparsePad c rows)) = d := by
  have hd' : IsDistance (rowSpace (sparsePad c rows)) d := (isDistance_padRows rows d).mpr hd
  have hS' := isotropic_padRows (m := padM c rows) rows hS
  refine ⟨sparsePad_sparse c hc rows, ?_⟩
  refine distanceOfPointU_correct _ hS' hd' (pointAt_pos _ h) (pointAt_le_one _ h)
    (one_le_pow₀ (by norm_num)) ?_ hA
  have h2 : 2 ^ (n + padM c rows + 1) * ((2 : ℚ) ^ h) ^ 2 * pointAt (n + padM c rows) h = 1 / 2 :=
    pointAt_small _ h
  have hpos : 0 < ((2 : ℚ) ^ h) ^ 2 * pointAt (n + padM c rows) h := by
    have := pointAt_pos (n + padM c rows) h
    positivity
  rw [pow_succ] at h2
  nlinarith

end QecPhysical.Stabilizer.DistanceExtraction

#print axioms QecPhysical.Stabilizer.DistanceExtraction.firstTrue_unique
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfTable_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfTable_correct_coeff
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfTable_correct_channel
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfPoint_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfPointU_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.isDistance_pad
#print axioms QecPhysical.Stabilizer.DistanceExtraction.infidelity_pad
#print axioms QecPhysical.Stabilizer.DistanceExtraction.uncorrectableProb_pad
#print axioms QecPhysical.Stabilizer.DistanceExtraction.isDistance_padRows
#print axioms QecPhysical.Stabilizer.DistanceExtraction.sparsePad_sparse
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_sparsehard_extraction
#print axioms QecPhysical.Stabilizer.DistanceExtraction.pointAt_small
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_pointhard_extraction
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_pointhard_extractionU
