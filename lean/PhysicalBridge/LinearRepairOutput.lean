import PhysicalBridge.LinearRepairBounds

/-! The once-prepared SAT cache followed by the measured single-pass repair.
The retained report contains counters only, not a duplicate output list. -/
namespace QecReliability.RationalOutput.LinearRepair
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

structure Report where
  pairVisits : ℕ
  ratioBuilds : ℕ
  orderComparisons : ℕ
  endpointTests : ℕ
  maxAccumulatorDen : ℕ

def Result.report (result : Result) : Report :=
  ⟨result.pairVisits,result.ratioBuilds,result.orderComparisons,result.endpointTests,result.maxAccumulatorDen⟩

def Report.payload (report : Report) : ℕ :=
  report.pairVisits.size+report.ratioBuilds.size+report.orderComparisons.size+
    report.endpointTests.size+report.maxAccumulatorDen.size

structure Output (r : ℕ) where
  raw : CoefficientTable r
  coefficients : Vector r
  report : Report

def prepare {Ω : Type*} [Fintype Ω] {n r : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) : Output r :=
  let T := prepareRational rows C H K solver a b c d ω
  let result := fromCache shape rows C T
  ⟨T,⟨result.values.toArray,by simp [result,fromCache_length]⟩,result.report⟩

theorem prepare_raw {Ω : Type*} [Fintype Ω] {n r : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) :
    (prepare shape rows C H K solver a b c d ω).raw=prepareRational rows C H K solver a b c d ω := rfl

theorem prepare_coefficients {Ω : Type*} [Fintype Ω] {n r : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) :
    (prepare shape rows C H K solver a b c d ω).coefficients=
      if shape then shapeVector rows C (prepareRational rows C H K solver a b c d ω)
      else endpointVector rows C (prepareRational rows C H K solver a b c d ω) :=
  vector_eq shape rows C _

theorem fromCache_report_payload {n r B : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n) (T : CoefficientTable r)
    (hT : ∀ j, (T.good.get j).1≤trialValueBound (keySize n r) B ∧
      (T.bad.get j).1≤trialValueBound (keySize n r) B) :
    (fromCache shape rows C T).report.payload≤
      4*(2*(r+1)).size+(2*trialValueBound (keySize n r) B).size := by
  have h0 := Nat.size_le_size (show (fromCache shape rows C T).pairVisits≤2*(r+1) by
    rw [fromCache_visits]; omega)
  have h := fromCache_bounds shape rows C T
  have h1 := Nat.size_le_size (h.1.trans (show r+1≤2*(r+1) by omega))
  have h2 := Nat.size_le_size h.2.1
  have h3 := Nat.size_le_size h.2.2
  have h4 := Nat.size_le_size (fromCache_accumulator_bound shape rows C T hT)
  dsimp only [Result.report,Report.payload]
  omega

end QecReliability.RationalOutput.LinearRepair
