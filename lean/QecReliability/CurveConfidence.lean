import QecReliability.QuantumBridge
import QecReliability.SimultaneousConfidence

/-! The confidence chain composed with the algebraic quantum reliability bridge.
Model sets below are canonical finite sets of distinct (latent cause, Pauli) pairs.
They are not an implementation or size certificate for the existential CNF compiler. -/

noncomputable section
namespace QecReliability.Binary

abbrev CoefficientIndex (r : ℕ) := Bool × Fin (r + 1)
abbrev CoefficientKey (n r : ℕ) := Causes r × Pauli n

def coefficientPredicate {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (side : Bool) (b : Causes r) (z : Pauli n) : Prop :=
  if side then Good (F := Bit) (symplectic n) S (supported (C b)) z
  else Bad (F := Bit) (symplectic n) S (supported (C b)) z

def coefficientModels {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (i : CoefficientIndex r) : Finset (CoefficientKey n r) := by
  classical
  exact Finset.univ.filter (fun bz => hammingLayer bz.1 = i.2 ∧
    bz.2 ∈ normalizer (F := Bit) (symplectic n) S ∧ coefficientPredicate S C i.1 bz.1 bz.2)

theorem coefficientModels_card {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (i : CoefficientIndex r) :
    (coefficientModels S C i).card = if i.1 then goodCoefficient S C i.2 else badCoefficient S C i.2 := by
  classical
  let T := {bz : {b : Causes r // hammingLayer b = i.2} ×
      normalizer (F := Bit) (symplectic n) S // coefficientPredicate S C i.1 bz.1 bz.2}
  let e : ↥(coefficientModels S C i) ≃ T :=
    { toFun := fun bz =>
        have h := (Finset.mem_filter.mp bz.property).2
        ⟨(⟨bz.val.1, h.1⟩, ⟨bz.val.2, h.2.1⟩), h.2.2⟩
      invFun := fun bz => ⟨(bz.val.1.val, bz.val.2.val), by
        simp only [coefficientModels, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨bz.val.1.property, bz.val.2.property, bz.property⟩⟩
      left_inv := by intro bz; rfl
      right_inv := by intro bz; rfl }
  have h := Nat.card_congr e
  rw [Nat.card_eq_finsetCard] at h
  cases hs : i.1 <;> simpa [T, coefficientPredicate, hs, goodCoefficient, badCoefficient] using h

theorem coefficientModels_bound {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (i : CoefficientIndex r) :
    (coefficientModels S C i).card ≤ 2 ^ (r + 2 * n) := by
  have h := Finset.card_le_univ (coefficientModels S C i)
  simpa [CoefficientKey, Causes, Pauli, Bit, Fintype.card_prod, Fintype.card_fun,
    ZMod.card, two_mul, pow_add] using h

def estimatedGood {Ω : Type*} [Fintype Ω] {n r : ℕ}
    {S : Submodule Bit (Pauli n)} {C : Causes r → Finset (Fin n)}
    {H : HashStages Ω (CoefficientKey n r) (r + 2 * n)}
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) (j : Fin (r + 1)) : ℝ :=
  ExactTrialOracle.amplified O B m ω (true, j)

def estimatedBad {Ω : Type*} [Fintype Ω] {n r : ℕ}
    {S : Submodule Bit (Pauli n)} {C : Causes r → Finset (Fin n)}
    {H : HashStages Ω (CoefficientKey n r) (r + 2 * n)}
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) (j : Fin (r + 1)) : ℝ :=
  ExactTrialOracle.amplified O B m ω (false, j)

/-- All layers and both positive counts succeed together. Zero counts stay exactly zero. -/
theorem coefficient_estimates_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (S : Submodule Bit (Pauli n)) (C : Causes r → Finset (Fin n))
    (H : HashStages Ω (CoefficientKey n r) (r + 2 * n))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ) (hB : 0 < B)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε / 3) ^ 2 * (B : ℝ))
    (hrepeat : (2 * (r + 1) : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      (∀ j, |estimatedGood O B m ω j - goodCoefficient S C j| ≤ (ε / 3) * goodCoefficient S C j) ∧
      (∀ j, |estimatedBad O B m ω j - badCoefficient S C j| ≤ (ε / 3) * badCoefficient S C j)) := by
  have hc := ExactTrialOracle.simultaneous_count_confidence O B m hB
    (coefficientModels_bound S C) (show 0 < ε / 3 by linarith) (show ε / 3 ≤ 1 by linarith)
    hcell (by simpa [CoefficientIndex] using hrepeat)
  apply hc.trans
  apply FiniteProbability.prob_mono
  intro ω h
  constructor
  · intro j
    simpa only [coefficientModels_card, Bool.true_eq, ↓reduceIte, estimatedGood] using h (true, j)
  · intro j
    simpa only [coefficientModels_card, Bool.false_eq_true, ↓reduceIte, estimatedBad] using h (false, j)

/-- The entire algebraic reliability curve and its complement have relative error at most ε
on one event of probability at least 1-δ. The circuit may be nonmonotone. -/
theorem latent_curve_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n))
    (H : HashStages Ω (CoefficientKey n r) (r + 2 * n))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ) (hB : 0 < B)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε / 3) ^ 2 * (B : ℝ))
    (hrepeat : (2 * (r + 1) : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve C (score S) p)
          (bernsteinCurve r (fun j => estimatedGood O B m ω j /
            (estimatedGood O B m ω j + estimatedBad O B m ω j)) p) ∧
        0 ≤ bernsteinCurve r (fun j => estimatedGood O B m ω j /
            (estimatedGood O B m ω j + estimatedBad O B m ω j)) p ∧
        bernsteinCurve r (fun j => estimatedGood O B m ω j /
            (estimatedGood O B m ω j + estimatedBad O B m ω j)) p ≤ 1) := by
  apply (coefficient_estimates_confidence S C H O B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω h p hp
  exact latent_curve_two_tail_relative S hS C ε hε.le hε1 _ _ h.1 h.2 p hp.1 hp.2

/-- The checked confidence chain INCLUDING shape repair, curve monotonicity, range and endpoints.
It does not identify the algebraic score with a channel optimum or verify a fast implementation. -/
theorem latent_curve_shape_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (hC : ∀ a b, a ⊆ b → C a ⊆ C b)
    (H : HashStages Ω (CoefficientKey n r) (r + 2 * n))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ) (hB : 0 < B)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε / 3) ^ 2 * (B : ℝ))
    (hrepeat : (2 * (r + 1) : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      AntitoneOn (shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω)) (Set.Icc 0 1) ∧
      shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) 0 = score S (C ∅) ∧
      shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) 1 = score S (C Finset.univ) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve C (score S) p)
          (shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) p) ∧
        score S (C Finset.univ) ≤ shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) p ∧
        shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) p ≤ score S (C ∅) ∧
        0 ≤ shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) p ∧
        shapeCorrectedCurve S C (estimatedGood O B m ω) (estimatedBad O B m ω) p ≤ 1) := by
  apply (coefficient_estimates_confidence S C H O B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω h
  exact latent_curve_shape_contract S hS C hC ε hε.le hε1 _ _ h.1 h.2

end QecReliability.Binary
