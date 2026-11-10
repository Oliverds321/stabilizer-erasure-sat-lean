import QecReliability.QuantumLatentEncoder

/-! Concrete quantum CNFs feed the proved confidence chain. Supplied hash circuits
must compute the explicit finite hash interface; their existence and speed are not asserted. -/
namespace QecReliability.SharedCircuit
open PrefixCNF

structure SuppliedHashCircuits {Ω A : Type*} [Fintype Ω] {q : ℕ}
    (H : HashStages Ω A q) (e : A ≃ BitModels q) where
  program : (s : Fin (q + 1)) → Ω → Program q s.val
  correct : ∀ s ω a, wordValue ((program s ω).eval (e a)) = (H.hash s ω a).val

theorem SuppliedHashCircuits.zero_correct {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {H : HashStages Ω A q} {e : A ≃ BitModels q} (K : SuppliedHashCircuits H e)
    (s : Fin (q + 1)) (ω : Ω) (a : BitModels q) :
    (K.program s ω).eval a = (fun _ => false) ↔ H.hash s ω (e.symm a) = zeroCell s.val := by
  have hc := K.correct s ω (e.symm a)
  rw [Equiv.apply_symm_apply] at hc
  have hz : wordValue (fun _ : Fin s.val => false) = 0 := by simp [wordValue]
  constructor
  · intro h
    rw [h, hz] at hc
    apply Fin.ext
    exact hc.symm
  · intro h
    apply wordValue_injective
    rw [hc, h, hz]
    rfl

namespace ConcreteQuantum
open LatentEncoding

def queries {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    (i : Binary.CoefficientIndex r) :
    DecisionQueries (keyBits n r) H (Binary.coefficientModels (rowSpace rows) (circuitMap C) i) where
  base :=
    { answer pre := (solver _).solve (PrefixCNF.restrict (quantumLayer rows C i).projectedFormula pre)
      correct pre := by
        rw [(solver _).correct _ (PrefixCNF.restrict_width (quantumLayer_contract rows C i).1 (by omega) pre),
          PrefixCNF.restrict_sat]
        simp only [PrefixEnumeration.PrefixSat, quantumLayer_projected] }
  cell s ω :=
    { answer pre := (solver _).solve (PrefixCNF.restrict
        (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre)
      correct pre := by
        rw [(solver _).correct _ (PrefixCNF.restrict_width
          (quantumCell_contract rows C i (K.program s ω) (fun _ => false)).1 (by omega) pre),
          PrefixCNF.restrict_sat]
        simp only [PrefixEnumeration.PrefixSat, quantumCell_projected, K.zero_correct] }

/-- Every hash-cell SAT query is a concrete width-three CNF with explicit total size.
The supplied hash circuit's gate count stays visible, rather than being assumed linear. -/
theorem query_size {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (i : Binary.CoefficientIndex r) (s : Fin (keySize n r + 1)) (ω : Ω) (pre : List Bool) :
    Width 3 (PrefixCNF.restrict
      (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre) ∧
    (PrefixCNF.restrict (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre).length ≤
      18 * rowIncidences rows + 22 * n + 83 * r + 4 * C.gates + 4 * (K.program s ω).gates + 53 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumCell rows C i (K.program s ω) (fun _ => false)).aux) ≤
      21 * r + 8 * n + 4 * rowIncidences rows + C.gates + (K.program s ω).gates + 12 := by
  have h := quantumCell_contract rows C i (K.program s ω) (fun _ => false)
  refine ⟨PrefixCNF.restrict_width h.1 (by omega) pre, ?_, h.2.2.1⟩
  have hl := PrefixCNF.restrict_length_bound
    (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre
  have hs := s.isLt
  unfold keySize at *
  omega

noncomputable def estimates {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    (ε δ : ℝ) (hδ : 0 < δ)
    (ω : Fin (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) → Ω)
    (i : Binary.CoefficientIndex r) : ℝ :=
  ExactTrialOracle.amplified (fun j => (queries rows C H K solver j).toTrialOracle)
    (cellBudget (ε / 3)) (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω i

theorem coefficients_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        (∀ j, |estimates rows C H K solver ε δ hδ ω (true, j) -
          Binary.goodCoefficient (rowSpace rows) (circuitMap C) j| ≤
          (ε / 3) * Binary.goodCoefficient (rowSpace rows) (circuitMap C) j) ∧
        (∀ j, |estimates rows C H K solver ε δ hδ ω (false, j) -
          Binary.badCoefficient (rowSpace rows) (circuitMap C) j| ≤
          (ε / 3) * Binary.badCoefficient (rowSpace rows) (circuitMap C) j)) := by
  have h := confidence_from_decisions (keyBits n r) H
    (Binary.coefficientModels (rowSpace rows) (circuitMap C)) (queries rows C H K solver)
    (show 0 < ε / 3 by linarith) (show ε / 3 ≤ 1 by linarith) hδ
  apply h.trans
  apply FiniteProbability.prob_mono
  intro ω hω
  constructor
  · intro j
    simpa only [Binary.coefficientModels_card, Bool.true_eq, ↓reduceIte, estimates] using hω (true, j)
  · intro j
    simpa only [Binary.coefficientModels_card, Bool.false_eq_true, ↓reduceIte, estimates] using hω (false, j)

/-- Whole-curve both-tail confidence now starts from supplied DAGs and an exact
concrete SAT solver. Isotropy enters the reliability-count bridge here. -/
theorem curve_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω => ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p)
          (bernsteinCurve r (fun j => estimates rows C H K solver ε δ hδ ω (true, j) /
            (estimates rows C H K solver ε δ hδ ω (true, j) +
              estimates rows C H K solver ε δ hδ ω (false, j))) p) ∧
        0 ≤ bernsteinCurve r (fun j => estimates rows C H K solver ε δ hδ ω (true, j) /
          (estimates rows C H K solver ε δ hδ ω (true, j) +
            estimates rows C H K solver ε δ hδ ω (false, j))) p ∧
        bernsteinCurve r (fun j => estimates rows C H K solver ε δ hδ ω (true, j) /
          (estimates rows C H K solver ε δ hδ ω (true, j) +
            estimates rows C H K solver ε δ hδ ω (false, j))) p ≤ 1) := by
  apply (coefficients_confidence rows C H K solver hε hε1 hδ).trans
  apply FiniteProbability.prob_mono
  intro ω hω p hp
  exact Binary.latent_curve_two_tail_relative (rowSpace rows) hS (circuitMap C) ε hε.le hε1
    _ _ hω.1 hω.2 p hp.1 hp.2

noncomputable def repairedCurve {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    (ε δ : ℝ) (hδ : 0 < δ)
    (ω : Fin (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) → Ω) : ℝ → ℝ :=
  Binary.shapeCorrectedCurve (rowSpace rows) (circuitMap C)
    (fun j => estimates rows C H K solver ε δ hδ ω (true, j))
    (fun j => estimates rows C H K solver ε δ hδ ω (false, j))

theorem shape_curve_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n) (hC : ∀ a b, a ⊆ b → circuitMap C a ⊆ circuitMap C b)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        AntitoneOn (repairedCurve rows C H K solver ε δ hδ ω) (Set.Icc 0 1) ∧
        repairedCurve rows C H K solver ε δ hδ ω 0 = Binary.score (rowSpace rows) (circuitMap C ∅) ∧
        repairedCurve rows C H K solver ε δ hδ ω 1 = Binary.score (rowSpace rows) (circuitMap C Finset.univ) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p)
            (repairedCurve rows C H K solver ε δ hδ ω p) ∧
          Binary.score (rowSpace rows) (circuitMap C Finset.univ) ≤ repairedCurve rows C H K solver ε δ hδ ω p ∧
          repairedCurve rows C H K solver ε δ hδ ω p ≤ Binary.score (rowSpace rows) (circuitMap C ∅) ∧
          0 ≤ repairedCurve rows C H K solver ε δ hδ ω p ∧ repairedCurve rows C H K solver ε δ hδ ω p ≤ 1) := by
  apply (coefficients_confidence rows C H K solver hε hε1 hδ).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  exact Binary.latent_curve_shape_contract (rowSpace rows) hS (circuitMap C) hC ε hε.le hε1
    _ _ hω.1 hω.2

end ConcreteQuantum
end QecReliability.SharedCircuit
