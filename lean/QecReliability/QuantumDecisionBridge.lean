import QecReliability.CurveConfidence
import QecReliability.DecisionTrial

/-! Explicit binary keys and the whole-curve theorem under prefix decision callbacks.
These equivalences do not prove a linear-size formula for the predicate being decided. -/

namespace QecReliability.Binary

def causeBits (r : ℕ) : Causes r ≃ BitModels r where
  toFun b i := decide (i ∈ b)
  invFun a := Finset.univ.filter (fun i => a i = true)
  left_inv b := by ext i; simp
  right_inv a := by funext i; cases h : a i <;> simp [h]

def bitBool : Bit ≃ Bool := (ZMod.finEquiv 2).toEquiv.symm.trans finTwoEquiv

def appendBits (p q : ℕ) : (BitModels p × BitModels q) ≃ BitModels (p + q) where
  toFun ab := Fin.append ab.1 ab.2
  invFun a := (fun i => a (Fin.castAdd q i), fun i => a (Fin.natAdd p i))
  left_inv ab := by
    apply Prod.ext <;> funext i <;> simp
  right_inv a := Fin.append_castAdd_natAdd

/-- Structural encoding: latent-set membership bits, followed by both binary Pauli coordinates. -/
def coefficientKeyBits (n r : ℕ) : CoefficientKey n r ≃ BitModels (r + 2 * n) :=
  ((causeBits r).prodCongr
      (((Equiv.piCongrRight (fun _ : Fin n => bitBool)).prodCongr
        (Equiv.piCongrRight (fun _ : Fin n => bitBool))).trans (appendBits n n))).trans
    ((appendBits r (n + n)).trans (Equiv.cast (by rw [Nat.two_mul])))

noncomputable section

def decisionGood {Ω : Type*} [Fintype Ω] {n r : ℕ}
    {S : Submodule Bit (Pauli n)} {C : Causes r → Finset (Fin n)}
    {H : HashStages Ω (CoefficientKey n r) (r + 2 * n)}
    (D : ∀ i, DecisionQueries (coefficientKeyBits n r) H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) : Fin (r + 1) → ℝ :=
  estimatedGood (fun i => (D i).toTrialOracle) B m ω

def decisionBad {Ω : Type*} [Fintype Ω] {n r : ℕ}
    {S : Submodule Bit (Pauli n)} {C : Causes r → Finset (Fin n)}
    {H : HashStages Ω (CoefficientKey n r) (r + 2 * n)}
    (D : ∀ i, DecisionQueries (coefficientKeyBits n r) H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) : Fin (r + 1) → ℝ :=
  estimatedBad (fun i => (D i).toTrialOracle) B m ω

/-- Whole-curve both-tail confidence assuming only exact prefix decision for the encoded predicates. -/
theorem latent_curve_confidence_from_decisions {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n))
    (H : HashStages Ω (CoefficientKey n r) (r + 2 * n))
    (D : ∀ i, DecisionQueries (coefficientKeyBits n r) H (coefficientModels S C i))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcell : 16 ≤ (ε / 3) ^ 2 * (B : ℝ))
    (hrepeat : (2 * (r + 1) : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve C (score S) p)
          (bernsteinCurve r (fun j => decisionGood D B m ω j /
            (decisionGood D B m ω j + decisionBad D B m ω j)) p) ∧
        0 ≤ bernsteinCurve r (fun j => decisionGood D B m ω j /
            (decisionGood D B m ω j + decisionBad D B m ω j)) p ∧
        bernsteinCurve r (fun j => decisionGood D B m ω j /
            (decisionGood D B m ω j + decisionBad D B m ω j)) p ≤ 1) :=
  latent_curve_confidence S hS C H (fun i => (D i).toTrialOracle) B m hB hε hε1 hcell hrepeat

/-- The same decision-only confidence chain with exact endpoints and monotonicity. -/
theorem latent_shape_confidence_from_decisions {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (hC : ∀ a b, a ⊆ b → C a ⊆ C b)
    (H : HashStages Ω (CoefficientKey n r) (r + 2 * n))
    (D : ∀ i, DecisionQueries (coefficientKeyBits n r) H (coefficientModels S C i))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcell : 16 ≤ (ε / 3) ^ 2 * (B : ℝ))
    (hrepeat : (2 * (r + 1) : ℝ) * (1 / 2 : ℝ) ^ (m + 2) ≤ δ) :
    1 - δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      AntitoneOn (shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω)) (Set.Icc 0 1) ∧
      shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) 0 = score S (C ∅) ∧
      shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) 1 = score S (C Finset.univ) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve C (score S) p)
          (shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) p) ∧
        score S (C Finset.univ) ≤ shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) p ∧
        shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) p ≤ score S (C ∅) ∧
        0 ≤ shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) p ∧
        shapeCorrectedCurve S C (decisionGood D B m ω) (decisionBad D B m ω) p ≤ 1) :=
  latent_curve_shape_confidence S hS C hC H (fun i => (D i).toTrialOracle) B m hB hε hε1 hcell hrepeat

end
end QecReliability.Binary
