import PhysicalBridge.PhysicalAlgorithm

/-! Values, exact zeros and confidence for the once-prepared table. No repair
or physical conclusion is assumed by these wrappers. -/
noncomputable section
namespace QecReliability.SharedCircuit.ConcreteQuantum
open LatentEncoding Binary

def CoefficientTable.value {r : ℕ} (T : CoefficientTable r) (i : CoefficientIndex r) : ℝ :=
  if i.1 then (T.good.get i.2).1 else (T.bad.get i.2).1

def CoefficientTable.ratio {r : ℕ} (T : CoefficientTable r) (j : Fin (r+1)) : ℝ :=
  T.value (true,j) / (T.value (true,j)+T.value (false,j))

theorem CoefficientTable.value_nonneg {r : ℕ} (T : CoefficientTable r) (i : CoefficientIndex r) :
    0≤T.value i := by unfold CoefficientTable.value; split <;> exact Nat.cast_nonneg _

theorem CoefficientTable.ratio_range {r : ℕ} (T : CoefficientTable r) (j : Fin (r+1)) :
    0≤T.ratio j ∧ T.ratio j≤1 := by
  have ha := T.value_nonneg (true,j)
  have hb := T.value_nonneg (false,j)
  unfold CoefficientTable.ratio
  exact ⟨div_nonneg ha (add_nonneg ha hb), div_le_one_of_le₀ (by linarith) (by linarith)⟩

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

theorem prepare_value (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : CoefficientIndex r) :
    (prepare rows C H K solver B m ω).value i =
      ExactTrialOracle.amplified (fun j => (queries rows C H K solver j).toTrialOracle) B m ω i := by
  rcases i with ⟨side,j⟩
  cases side <;> simp only [CoefficientTable.value, prepare_eq_cached, Bool.false_eq_true, ↓reduceIte,
    CountTable.get_build, DecisionQueries.cachedMedian_value, ExactTrialOracle.amplified]

theorem prepare_value_zero_iff (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : CoefficientIndex r) :
    (prepare rows C H K solver B m ω).value i = 0 ↔
      (coefficientModels (rowSpace rows) (circuitMap C) i).card = 0 := by
  rw [prepare_value, Finset.card_eq_zero]
  constructor
  · intro hz
    by_contra hn
    have hp := ExactTrialOracle.amplified_positive
      (fun j => (queries rows C H K solver j).toTrialOracle) B m ω i
      (Finset.nonempty_iff_ne_empty.mpr hn)
    linarith
  · exact ExactTrialOracle.amplified_zero
      (fun j => (queries rows C H K solver j).toTrialOracle) B m ω i

theorem prepare_total_pos (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Fin (r+1)) :
    0 < (prepare rows C H K solver B m ω).value (true,j) +
      (prepare rows C H K solver B m ω).value (false,j) := by
  have ha := (prepare rows C H K solver B m ω).value_nonneg (true,j)
  have hb := (prepare rows C H K solver B m ω).value_nonneg (false,j)
  by_contra hn
  have hza : (prepare rows C H K solver B m ω).value (true,j)=0 := by linarith
  have hzb : (prepare rows C H K solver B m ω).value (false,j)=0 := by linarith
  have hA := (prepare_value_zero_iff rows C H K solver B m ω (true,j)).mp hza
  have hB := (prepare_value_zero_iff rows C H K solver B m ω (false,j)).mp hzb
  simp only [coefficientModels_card, Bool.false_eq_true, ↓reduceIte] at hA hB
  have hp := coefficient_total_pos (rowSpace rows) (circuitMap C) j
  simp [hA,hB] at hp

/-- Parametric confidence, ready for later executable budget selection. -/
theorem prepare_coefficients_confidence (B m : ℕ) (hB : 0<B)
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hcell : 16≤(ε/3)^2*(B:ℝ))
    (hrepeat : (2*(r+1):ℝ)*(1/2:ℝ)^(m+2)≤δ) :
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      ∀ i, |(prepare rows C H K solver B m ω).value i -
        ((coefficientModels (rowSpace rows) (circuitMap C) i).card:ℝ)| ≤
        (ε/3)*(coefficientModels (rowSpace rows) (circuitMap C) i).card) := by
  have h := ExactTrialOracle.simultaneous_count_confidence
    (fun i => (queries rows C H K solver i).toTrialOracle) B m hB
    (fun i => by simpa [keySize,two_mul] using coefficientModels_bound (rowSpace rows) (circuitMap C) i)
    (show 0<ε/3 by linarith) (show ε/3≤1 by linarith) hcell
    (by simpa [CoefficientIndex] using hrepeat)
  simpa only [prepare_value] using h

end QecReliability.SharedCircuit.ConcreteQuantum
