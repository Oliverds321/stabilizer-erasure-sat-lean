import OracleCost.ScaleSelection
import OracleCost.MedianSort
import OracleCost.QuantumService

/-! A value-preserving implementation refinement of the actual coefficient
preparation: scale selection scans the retained list, and median sorting uses
the measured insertion sort. No baseline module or proof statement is changed.
-/
namespace QecReliability.OracleCost.CachedRefinement
open PrefixEnumeration
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/- Callback-only implementations retain the refined scan and insertion-sort median. -/
def trialFromAnswers {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q+1) → Ω → List Bool → Bool)
    (B : ℕ) (ω : Ω) : ℕ × ℕ :=
  if baseAnswer [] then
    let table := CountTable.build (fun s => enumerate q (cellAnswer s ω) (4*B+1))
    ((ScaleSelection.select B table).estimate,1+table.calls)
  else (0,1)

def medianFromAnswers {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q+1) → Ω → List Bool → Bool)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : ℕ × ℕ :=
  let table := CountTable.build (fun i => trialFromAnswers baseAnswer cellAnswer B (ω i))
  (MedianSort.median (fun i => (table.get i).1),table.calls)

variable {Ω A : Type*} [Fintype Ω] {q : ℕ} {e : A ≃ BitModels q}
    {H : HashStages Ω A q} {S : Finset A}

def trial (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) : ℕ × ℕ :=
  if D.base.answer [] then
    let table := CountTable.build (fun s => enumerate q (D.cell s ω).answer (4*B+1))
    ((ScaleSelection.select B table).estimate,1+table.calls)
  else (0,1)

theorem trial_eq (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    trial D B ω=D.cachedTrial B ω := by
  simp only [trial,DecisionQueries.cachedTrial,ScaleSelection.select_eq]

def median (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2*m+1) → Ω) : ℕ × ℕ :=
  let table := CountTable.build (fun i => trial D B (ω i))
  (MedianSort.median (fun i => (table.get i).1),table.calls)

theorem median_eq (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    median D B m ω=D.cachedMedian B m ω := by
  simp only [median,trial_eq,DecisionQueries.cachedMedian,MedianSort.median_eq]

def prepare {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : CoefficientTable r :=
  ⟨CountTable.build (fun j =>
      let D := queries rows C H K solver (true,j)
      medianFromAnswers D.base.answer (fun s seed => (D.cell s seed).answer) B m ω),
   CountTable.build (fun j =>
      let D := queries rows C H K solver (false,j)
      medianFromAnswers D.base.answer (fun s seed => (D.cell s seed).answer) B m ω)⟩

theorem prepare_eq_median {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    prepare rows C H K solver B m ω =
      ⟨CountTable.build (fun j => median (queries rows C H K solver (true,j)) B m ω),
       CountTable.build (fun j => median (queries rows C H K solver (false,j)) B m ω)⟩ := rfl

theorem prepare_eq {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    prepare rows C H K solver B m ω=ConcreteQuantum.prepare rows C H K solver B m ω := by
  simp only [prepare_eq_median,median_eq,ConcreteQuantum.prepare_eq_cached]

/-- The refined table is the very same table underlying the measured physical
output. Construction, indexed access and machine allocation still need costs. -/
theorem prepare_measured {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    prepare rows C H K service.solver B m ω=
      (QuantumService.prepareMeasured rows C H K service B m ω).erase := by
  rw [prepare_eq,QuantumService.prepareMeasured_erase]

end QecReliability.OracleCost.CachedRefinement
