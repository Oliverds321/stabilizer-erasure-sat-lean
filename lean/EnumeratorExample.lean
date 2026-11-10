import PhysicalBridge.AmbiguityRank
import PhysicalBridge.ExactEndpoints
import PhysicalBridge.PhysicalBernstein
import PhysicalBridge.GeneralStabilizer
import UncorrectableProbability

set_option autoImplicit false

/-!
# Ordinary weight enumerators do not determine the erasure curve

Two three-qubit stabilizer codes:

* code R: checks `Z₁Z₂`, `Z₂Z₃` (rows `[inr 0, inr 1]`, `[inr 1, inr 2]`);
* code B: checks `X₁X₂`, `Z₁Z₂` (rows `[inl 0, inl 1]`, `[inr 0, inr 1]`), a Bell pair on
  qubits 1,2 and a free qubit 3.

E1. Per-pattern ambiguities/scores (computed by the kernel from the computable rank routine
    `ambiguityRank`) and the layer sums of the score.
E2. The iid erasure curves `∑ E, causeMass p E * erasureScore S E`, their difference
    `(3/4) p (1-p)^2`, and the same statement for the actual physical channel (isotropic lift).
E3. Equal ordinary weight enumerators of the stabilizer spaces and of the normalizers.
Extras: repetition code, one unencoded qubit (`I(p) = 3p/4`, `U(p) = p`), and the correctable
erased sets of a four-qubit CSS code.
-/

noncomputable section

namespace QecPhysical.Stabilizer.EnumeratorExample

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.BinaryElimination

/-! ## The two codes -/

/-- Code R: checks `Z₁Z₂`, `Z₂Z₃`. -/
def rowsR : List (List (PauliCoord 3)) := [[.inr 0, .inr 1], [.inr 1, .inr 2]]

/-- Code B: checks `X₁X₂`, `Z₁Z₂` (Bell pair on qubits 1,2, free qubit 3). -/
def rowsB : List (List (PauliCoord 3)) := [[.inl 0, .inl 1], [.inr 0, .inr 1]]

/-! ## General helpers -/

theorem ambiguity_eq_rank {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambiguity (symplectic n) (rowSpace rows) (supported E) = ambiguityRank rows E :=
  (ambiguityRank_correct rows E).symm

theorem erasureScore_eq_rank {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    erasureScore (rowSpace rows) E = ((2 : ℝ) ^ ambiguityRank rows E)⁻¹ := by
  rw [ambiguityRank_correct]
  rfl

theorem erasureScore_eq_scoreRat {n : ℕ} (rows : List (List (PauliCoord n)))
    (E : Finset (Fin n)) : erasureScore (rowSpace rows) E = (scoreRat rows E : ℝ) :=
  (scoreRat_correct rows E).symm

theorem inv_two_pow_eq_one_iff (k : ℕ) : ((2 : ℝ) ^ k)⁻¹ = 1 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have h1 : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) hk
    have h2 : (2 : ℝ) ^ k = 1 := by
      have := congrArg (·⁻¹) h
      simpa using this
    linarith
  · rintro rfl
    simp

/-- Computable natural-number layer sum: `4 ×` the score layer sum when all ambiguities are
at most `2`. -/
def layerSumN {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) : ℕ :=
  ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), 2 ^ (2 - ambiguityRank rows E)

theorem layerSum_eq_nat {n : ℕ} (rows : List (List (PauliCoord n)))
    (h : ∀ E : Finset (Fin n), ambiguityRank rows E ≤ 2) (j : ℕ) :
    ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), erasureScore (rowSpace rows) E =
      (layerSumN rows j : ℝ) / 4 := by
  rw [layerSumN, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  rw [erasureScore_eq_rank]
  have hk := h E
  generalize ambiguityRank rows E = k at hk ⊢
  interval_cases k <;> norm_num

/-- Grouping the iid erasure sum by the size of the erased set. -/
theorem causeMass_sum_layers {n : ℕ} (f : Finset (Fin n) → ℝ) (p : ℝ) :
    ∑ E : Finset (Fin n), causeMass p E * f E =
      ∑ j ∈ range (n + 1), p ^ j * (1 - p) ^ (n - j) *
        ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), f E := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (Finset (Fin n))))
    (t := range (n + 1)) (g := Finset.card)
    (fun E _ => by simpa [Nat.lt_succ_iff] using E.card_le_univ)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun E hE => ?_)
  rw [causeMass, (Finset.mem_filter.mp hE).2]

/-! ## E1. Per-pattern ambiguities and scores -/

/-- Code R: ambiguity `0` on `∅`, `2` on all three qubits, `1` otherwise. -/
theorem ambiguityRank_R : ∀ E : Finset (Fin 3),
    ambiguityRank rowsR E = if E = ∅ then 0 else if E = univ then 2 else 1 := by
  decide

/-- Code B: ambiguity `2` if qubit 3 is erased, `0` otherwise. -/
theorem ambiguityRank_B : ∀ E : Finset (Fin 3),
    ambiguityRank rowsB E = if (2 : Fin 3) ∈ E then 2 else 0 := by
  decide

theorem scoreRat_R (E : Finset (Fin 3)) :
    scoreRat rowsR E = if E = ∅ then 1 else if E = univ then 1/4 else 1/2 := by
  rw [scoreRat, scorePair, ambiguityRank_R]
  split_ifs <;> norm_num

theorem scoreRat_B (E : Finset (Fin 3)) :
    scoreRat rowsB E = if (2 : Fin 3) ∈ E then 1/4 else 1 := by
  rw [scoreRat, scorePair, ambiguityRank_B]
  split_ifs <;> norm_num

theorem erasureScore_R (E : Finset (Fin 3)) :
    erasureScore (rowSpace rowsR) E = if E = ∅ then 1 else if E = univ then 1/4 else 1/2 := by
  rw [erasureScore_eq_rank, ambiguityRank_R]
  split_ifs <;> norm_num

theorem erasureScore_B (E : Finset (Fin 3)) :
    erasureScore (rowSpace rowsB) E = if (2 : Fin 3) ∈ E then 1/4 else 1 := by
  rw [erasureScore_eq_rank, ambiguityRank_B]
  split_ifs <;> norm_num

theorem ambiguityRank_R_le : ∀ E : Finset (Fin 3), ambiguityRank rowsR E ≤ 2 := by decide
theorem ambiguityRank_B_le : ∀ E : Finset (Fin 3), ambiguityRank rowsB E ≤ 2 := by decide

theorem layerSumN_R : layerSumN rowsR 0 = 4 ∧ layerSumN rowsR 1 = 6 ∧
    layerSumN rowsR 2 = 6 ∧ layerSumN rowsR 3 = 1 := by
  decide

theorem layerSumN_B : layerSumN rowsB 0 = 4 ∧ layerSumN rowsB 1 = 9 ∧
    layerSumN rowsB 2 = 6 ∧ layerSumN rowsB 3 = 1 := by
  decide

/-- Layer sums of the score for code R: `1, 3/2, 3/2, 1/4`. -/
theorem layerSum_R :
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 0), erasureScore (rowSpace rowsR) E = 1 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 1), erasureScore (rowSpace rowsR) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 2), erasureScore (rowSpace rowsR) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 3), erasureScore (rowSpace rowsR) E = 1/4 := by
  obtain ⟨h0, h1, h2, h3⟩ := layerSumN_R
  simp only [layerSum_eq_nat rowsR ambiguityRank_R_le, h0, h1, h2, h3]
  norm_num

/-- Layer sums of the score for code B: `1, 9/4, 3/2, 1/4`. -/
theorem layerSum_B :
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 0), erasureScore (rowSpace rowsB) E = 1 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 1), erasureScore (rowSpace rowsB) E = 9/4 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 2), erasureScore (rowSpace rowsB) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 3), erasureScore (rowSpace rowsB) E = 1/4 := by
  obtain ⟨h0, h1, h2, h3⟩ := layerSumN_B
  simp only [layerSum_eq_nat rowsB ambiguityRank_B_le, h0, h1, h2, h3]
  norm_num

/-! ## E2. The curves differ -/

theorem curve_R (p : ℝ) :
    ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsR) E =
      (1 - p) ^ 3 + (3/2) * p * (1 - p) ^ 2 + (3/2) * p ^ 2 * (1 - p) + (1/4) * p ^ 3 := by
  obtain ⟨h0, h1, h2, h3⟩ := layerSum_R
  rw [causeMass_sum_layers]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]
  norm_num
  ring

theorem curve_B (p : ℝ) :
    ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsB) E = 1 - (3/4) * p := by
  obtain ⟨h0, h1, h2, h3⟩ := layerSum_B
  rw [causeMass_sum_layers]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]
  norm_num
  ring

theorem curve_difference (p : ℝ) :
    ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsB) E -
      ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsR) E =
        (3/4) * p * (1 - p) ^ 2 := by
  rw [curve_B, curve_R]
  ring

theorem curves_differ {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsB) E ≠
      ∑ E : Finset (Fin 3), causeMass p E * erasureScore (rowSpace rowsR) E := by
  intro h
  have hd := curve_difference p
  rw [h, sub_self] at hd
  have : 0 < (3/4) * p * (1 - p) ^ 2 := by
    have : 0 < 1 - p := by linarith
    positivity
  linarith

/-! ### Isotropy and the physical channel -/

theorem rowSpace_isotropic_of {n : ℕ} (rows : List (List (PauliCoord n)))
    (h : ∀ r ∈ rows, ∀ r' ∈ rows, symplectic n (decodeRow r') (decodeRow r) = 0) :
    rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows) := by
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact (mem_normalizer_rows rows (decodeRow r)).2 (fun r' hr' => h r hr r' hr')

theorem isotropic_R : rowSpace rowsR ≤ normalizer (symplectic 3) (rowSpace rowsR) :=
  rowSpace_isotropic_of rowsR (by decide)

theorem isotropic_B : rowSpace rowsB ≤ normalizer (symplectic 3) (rowSpace rowsB) :=
  rowSpace_isotropic_of rowsB (by decide)

def liftR : Lift (rowSpace rowsR) := isotropicLift _ isotropic_R
def liftB : Lift (rowSpace rowsB) := isotropicLift _ isotropic_B

/-- Physical optimum for code R under iid erasure (one latent bit per qubit). -/
theorem physical_R (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (liftR.erasureFlagDecoder.comp
        (liftR.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map =
      (1 - p) ^ 3 + (3/2) * p * (1 - p) ^ 2 + (3/2) * p ^ 2 * (1 - p) + (1/4) * p ^ 3 ∧
    ∀ Q : Channel (ErasureFlagOutput 3) liftR.LogicalIndex,
      entanglementFidelity (Q.comp (liftR.iidLatentErasure id p hp hp1)).map ≤
        (1 - p) ^ 3 + (3/2) * p * (1 - p) ^ 2 + (3/2) * p ^ 2 * (1 - p) + (1/4) * p ^ 3 := by
  have h := liftR.iidLatentErasure_optimum (id : Causes 3 → Finset (Fin 3)) p hp hp1
  rw [← latentCurve_eq_bernstein] at h
  have hc : latentCurve (id : Causes 3 → Finset (Fin 3)) (erasureScore (rowSpace rowsR)) p =
      (1 - p) ^ 3 + (3/2) * p * (1 - p) ^ 2 + (3/2) * p ^ 2 * (1 - p) + (1/4) * p ^ 3 :=
    curve_R p
  rw [hc] at h
  exact h

/-- Physical optimum for code B under iid erasure: `1 - 3p/4`. -/
theorem physical_B (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (liftB.erasureFlagDecoder.comp
        (liftB.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map = 1 - (3/4) * p ∧
    ∀ Q : Channel (ErasureFlagOutput 3) liftB.LogicalIndex,
      entanglementFidelity (Q.comp (liftB.iidLatentErasure id p hp hp1)).map ≤ 1 - (3/4) * p := by
  have h := liftB.iidLatentErasure_optimum (id : Causes 3 → Finset (Fin 3)) p hp hp1
  rw [← latentCurve_eq_bernstein] at h
  have hc : latentCurve (id : Causes 3 → Finset (Fin 3)) (erasureScore (rowSpace rowsB)) p =
      1 - (3/4) * p := curve_B p
  rw [hc] at h
  exact h

/-- The optimal physical fidelities differ by `(3/4) p (1-p)^2`. -/
theorem physical_difference (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (liftB.erasureFlagDecoder.comp
        (liftB.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map -
      entanglementFidelity (liftR.erasureFlagDecoder.comp
        (liftR.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map =
      (3/4) * p * (1 - p) ^ 2 := by
  rw [(physical_B p hp hp1).1, (physical_R p hp hp1).1]
  ring

/-! ## E3. Equal ordinary weight enumerators -/

/-- Pauli weight: number of qubits on which `v` acts nontrivially. -/
def pauliWeight {n : ℕ} (v : Pauli n) : ℕ :=
  (univ.filter (fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0)).card

theorem pauliWeight_le {n : ℕ} (v : Pauli n) : pauliWeight v ≤ n := by
  simpa [pauliWeight] using card_le_univ (univ.filter (fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0))

open Classical in
/-- Number of elements of weight `w` in a subspace `T` of `Pauli n`. -/
def weightCount {n : ℕ} (T : Submodule Bit (Pauli n)) (w : ℕ) : ℕ :=
  (univ.filter (fun v : Pauli n => v ∈ T ∧ pauliWeight v = w)).card

theorem weightCount_eq_zero {n : ℕ} (T : Submodule Bit (Pauli n)) {w : ℕ} (hw : n < w) :
    weightCount T w = 0 := by
  classical
  unfold weightCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  have := pauliWeight_le v
  omega

theorem mem_rowSpace_pair {n : ℕ} (r₁ r₂ : List (PauliCoord n)) (v : Pauli n) :
    v ∈ rowSpace [r₁, r₂] ↔ ∃ c d : Bit, c • decodeRow r₁ + d • decodeRow r₂ = v := by
  have hs : {x | x ∈ [r₁, r₂].map decodeRow} = ({decodeRow r₁, decodeRow r₂} : Set (Pauli n)) := by
    ext x
    simp
  rw [rowSpace, hs, Submodule.mem_span_pair]

/-- Decidable description of the counts in a two-row stabilizer space. -/
theorem weightCount_rowSpace_pair {n : ℕ} (r₁ r₂ : List (PauliCoord n)) (w : ℕ) :
    weightCount (rowSpace [r₁, r₂]) w =
      (univ.filter (fun v : Pauli n =>
        (∃ c d : Bit, c • decodeRow r₁ + d • decodeRow r₂ = v) ∧ pauliWeight v = w)).card := by
  classical
  unfold weightCount
  congr 1
  exact Finset.filter_congr (fun v _ => by rw [mem_rowSpace_pair])

/-- Decidable description of the counts in the normalizer of a row space. -/
theorem weightCount_normalizer {n : ℕ} (rows : List (List (PauliCoord n))) (w : ℕ) :
    weightCount (normalizer (symplectic n) (rowSpace rows)) w =
      (univ.filter (fun v : Pauli n =>
        (∀ row ∈ rows, symplectic n (decodeRow row) v = 0) ∧ pauliWeight v = w)).card := by
  classical
  unfold weightCount
  congr 1
  exact Finset.filter_congr (fun v _ => by rw [mem_normalizer_rows])

/-- Stabilizer weight enumerator of code R: `1, 0, 3, 0`. -/
theorem stabilizer_counts_R :
    weightCount (rowSpace rowsR) 0 = 1 ∧ weightCount (rowSpace rowsR) 1 = 0 ∧
    weightCount (rowSpace rowsR) 2 = 3 ∧ weightCount (rowSpace rowsR) 3 = 0 := by
  simp only [rowsR, weightCount_rowSpace_pair]
  decide

/-- Stabilizer weight enumerator of code B: `1, 0, 3, 0`. -/
theorem stabilizer_counts_B :
    weightCount (rowSpace rowsB) 0 = 1 ∧ weightCount (rowSpace rowsB) 1 = 0 ∧
    weightCount (rowSpace rowsB) 2 = 3 ∧ weightCount (rowSpace rowsB) 3 = 0 := by
  simp only [rowsB, weightCount_rowSpace_pair]
  decide

/-- Normalizer weight enumerator of code R: `1, 3, 3, 9`. -/
theorem normalizer_counts_R :
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) 0 = 1 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) 1 = 3 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) 2 = 3 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) 3 = 9 := by
  simp only [weightCount_normalizer, rowsR]
  decide

/-- Normalizer weight enumerator of code B: `1, 3, 3, 9`. -/
theorem normalizer_counts_B :
    weightCount (normalizer (symplectic 3) (rowSpace rowsB)) 0 = 1 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsB)) 1 = 3 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsB)) 2 = 3 ∧
    weightCount (normalizer (symplectic 3) (rowSpace rowsB)) 3 = 9 := by
  simp only [weightCount_normalizer, rowsB]
  decide

theorem weightCount_eq_of_table {T T' : Submodule Bit (Pauli 3)}
    (h : ∀ w ≤ 3, weightCount T w = weightCount T' w) (w : ℕ) :
    weightCount T w = weightCount T' w := by
  by_cases hw : 3 < w
  · rw [weightCount_eq_zero T hw, weightCount_eq_zero T' hw]
  · exact h w (by omega)

/-- Equal stabilizer weight enumerators. -/
theorem stabilizer_enumerators_eq (w : ℕ) :
    weightCount (rowSpace rowsR) w = weightCount (rowSpace rowsB) w := by
  obtain ⟨a0, a1, a2, a3⟩ := stabilizer_counts_R
  obtain ⟨b0, b1, b2, b3⟩ := stabilizer_counts_B
  refine weightCount_eq_of_table (fun w hw => ?_) w
  interval_cases w <;> simp [a0, a1, a2, a3, b0, b1, b2, b3]

/-- Equal normalizer weight enumerators. -/
theorem normalizer_enumerators_eq (w : ℕ) :
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) w =
      weightCount (normalizer (symplectic 3) (rowSpace rowsB)) w := by
  obtain ⟨a0, a1, a2, a3⟩ := normalizer_counts_R
  obtain ⟨b0, b1, b2, b3⟩ := normalizer_counts_B
  refine weightCount_eq_of_table (fun w hw => ?_) w
  interval_cases w <;> simp [a0, a1, a2, a3, b0, b1, b2, b3]

/-! ## Extras -/

/-- Three-qubit repetition code (rows of code R): one erased qubit has ambiguity 1. -/
theorem repetition_single : ∀ i : Fin 3, ambiguityRank rowsR {i} = 1 := by decide

theorem repetition_single_score (i : Fin 3) : erasureScore (rowSpace rowsR) {i} = 1/2 := by
  rw [erasureScore_eq_rank, repetition_single]
  norm_num

/-- One unencoded qubit: no rows. -/
def rowsBare : List (List (PauliCoord 1)) := []

theorem bare_ambiguity : ambiguityRank rowsBare {0} = 2 := by decide

theorem bare_score : erasureScore (rowSpace rowsBare) {0} = 1/4 := by
  rw [erasureScore_eq_rank, bare_ambiguity]
  norm_num

theorem univ_fin_one_finsets : (univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide

open Uncorrectable in
/-- One unencoded qubit: optimal infidelity `3p/4`. -/
theorem bare_infidelity (p : ℝ) : infidelity (rowSpace rowsBare) p = (3/4) * p := by
  have h0 : ambiguityRank rowsBare ∅ = 0 := by decide
  unfold infidelity
  rw [univ_fin_one_finsets, Finset.sum_pair (by decide)]
  simp only [infidelityScore, erasureScore_eq_rank, h0, bare_ambiguity, causeMass,
    Finset.card_empty, Finset.card_singleton]
  norm_num
  ring

open Uncorrectable in
/-- One unencoded qubit: uncorrectable probability `p`. -/
theorem bare_uncorrectableProb (p : ℝ) : uncorrectableProb (rowSpace rowsBare) p = p := by
  have h0 : ambiguityRank rowsBare ∅ = 0 := by decide
  unfold uncorrectableProb
  rw [univ_fin_one_finsets, Finset.sum_pair (by decide)]
  simp only [uncorrectable, ambiguity_eq_rank, h0, bare_ambiguity, causeMass,
    Finset.card_empty, Finset.card_singleton]
  norm_num

/-- Four-qubit CSS code with checks `Z₁Z₂Z₄`, `X₁X₃X₄`, `X₁X₂X₃`. -/
def rows4 : List (List (PauliCoord 4)) :=
  [[.inr 0, .inr 1, .inr 3], [.inl 0, .inl 2, .inl 3], [.inl 0, .inl 1, .inl 2]]

theorem isotropic_4 : rowSpace rows4 ≤ normalizer (symplectic 4) (rowSpace rows4) :=
  rowSpace_isotropic_of rows4 (by decide)

/-- Correctable erased sets of the four-qubit code: exactly `∅, {1}, {2}, {4}, {2,4}`
(1-indexed), i.e. `∅, {0}, {1}, {3}, {1,3}` in `Fin 4`. -/
theorem four_correctable (E : Finset (Fin 4)) :
    erasureScore (rowSpace rows4) E = 1 ↔
      E ∈ ({∅, {0}, {1}, {3}, {1, 3}} : Finset (Finset (Fin 4))) := by
  rw [erasureScore_eq_rank, inv_two_pow_eq_one_iff]
  revert E
  decide

end QecPhysical.Stabilizer.EnumeratorExample

#print axioms QecPhysical.Stabilizer.EnumeratorExample.erasureScore_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.erasureScore_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.layerSum_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.layerSum_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.curve_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.curve_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.curve_difference
#print axioms QecPhysical.Stabilizer.EnumeratorExample.curves_differ
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_difference
#print axioms QecPhysical.Stabilizer.EnumeratorExample.stabilizer_counts_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.stabilizer_counts_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.normalizer_counts_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.normalizer_counts_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.stabilizer_enumerators_eq
#print axioms QecPhysical.Stabilizer.EnumeratorExample.normalizer_enumerators_eq
#print axioms QecPhysical.Stabilizer.EnumeratorExample.repetition_single_score
#print axioms QecPhysical.Stabilizer.EnumeratorExample.bare_infidelity
#print axioms QecPhysical.Stabilizer.EnumeratorExample.bare_uncorrectableProb
#print axioms QecPhysical.Stabilizer.EnumeratorExample.four_correctable
