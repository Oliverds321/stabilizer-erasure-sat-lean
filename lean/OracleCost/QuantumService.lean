import OracleCost.CachedBatch
import OracleCost.ServiceAdapter
import PhysicalBridge.LinearRepairConfidence

/-! Actual quantum requests, measured coefficient preparation, and erasure back
to the existing estimator. All counters are ghost measurements. This module
charges service invocations; it does not identify callback time with total time.
-/
namespace QecReliability.OracleCost.QuantumService
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open CachedControl

/- Callback-only forms avoid passing a semantic model set to executable code. -/
def measuredTrial {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q + 1) → Ω → List Bool → Bool)
    (B : ℕ) (ω : Ω) (baseCharge : ℕ)
    (charge : Fin (q + 1) → List Bool → ℕ) : TrialResult :=
  if baseAnswer [] then
    let entries := List.ofFn (fun s => PrefixControl.run q (cellAnswer s ω) (charge s) (4*B+1))
    let cache : CountTable (q+1) :=
      ⟨entries.map (fun x => (x.count,x.calls)),by simp [entries]⟩
    ⟨selectCached B cache,1+cache.calls,
      baseCharge+(entries.map PrefixControl.Result.oracleTime).sum,
      (entries.map PrefixControl.Result.visits).sum⟩
  else ⟨0,1,baseCharge,0⟩

def measuredMedian {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q + 1) → Ω → List Bool → Bool)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω)
    (baseCharge : Ω → ℕ) (charge : Ω → Fin (q+1) → List Bool → ℕ) : TrialResult :=
  let trials := MeasuredTable.build (fun i =>
    measuredTrial baseAnswer cellAnswer B (ω i) (baseCharge (ω i)) (charge (ω i)))
  let values := trials.erase
  ⟨oddNatMedian (fun i => (values.get i).1),values.calls,trials.oracleTime,trials.prefixVisits⟩

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))

def baseRequest (i : CoefficientIndex r) (pre : List Bool) : SATRequest :=
  ⟨_, PrefixCNF.restrict (quantumLayer rows C i).projectedFormula pre,
    PrefixCNF.restrict_width (quantumLayer_contract rows C i).1 (by omega) pre⟩

def cellRequest (i : CoefficientIndex r) (s : Fin (keySize n r+1))
    (ω : Ω) (pre : List Bool) : SATRequest :=
  ⟨_,PrefixCNF.restrict (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre,
    PrefixCNF.restrict_width
      (quantumCell_contract rows C i (K.program s ω) (fun _ => false)).1 (by omega) pre⟩

variable (service : SATService)

theorem base_answer (i : CoefficientIndex r) (pre : List Bool) :
    (queries rows C H K service.solver i).base.answer pre =
      (service.run (baseRequest rows C i pre)).value := by
  exact service.solve_width _ _

theorem cell_answer (i : CoefficientIndex r) (s : Fin (keySize n r+1))
    (ω : Ω) (pre : List Bool) :
    ((queries rows C H K service.solver i).cell s ω).answer pre =
      (service.run (cellRequest rows C H K i s ω pre)).value := by
  exact service.solve_width _ _

structure MeasuredCoefficients (r : ℕ) where
  good : MeasuredTable (r+1)
  bad : MeasuredTable (r+1)

def MeasuredCoefficients.erase (T : MeasuredCoefficients r) : CoefficientTable r :=
  ⟨T.good.erase,T.bad.erase⟩
def MeasuredCoefficients.oracleTime (T : MeasuredCoefficients r) : ℕ :=
  T.good.oracleTime+T.bad.oracleTime

def coefficient (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : CoefficientIndex r) : TrialResult :=
  let D := queries rows C H K service.solver i
  measuredMedian D.base.answer (fun s seed => (D.cell s seed).answer) B m ω
    (fun _ => (service.run (baseRequest rows C i [])).time)
    (fun seed s pre => (service.run (cellRequest rows C H K i s seed pre)).time)

theorem coefficient_eq_median (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : CoefficientIndex r) :
    coefficient rows C H K service B m ω i =
      median (queries rows C H K service.solver i) B m ω
        (fun _ => (service.run (baseRequest rows C i [])).time)
        (fun seed s pre => (service.run (cellRequest rows C H K i s seed pre)).time) := rfl

def prepareMeasured (B m : ℕ) (ω : Fin (2*m+1) → Ω) : MeasuredCoefficients r :=
  ⟨MeasuredTable.build (fun j => coefficient rows C H K service B m ω (true,j)),
   MeasuredTable.build (fun j => coefficient rows C H K service B m ω (false,j))⟩

theorem coefficient_erase (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : CoefficientIndex r) :
    (coefficient rows C H K service B m ω i).estimate=
      ((queries rows C H K service.solver i).cachedMedian B m ω).1 ∧
    (coefficient rows C H K service B m ω i).calls=
      ((queries rows C H K service.solver i).cachedMedian B m ω).2 := by
  rw [coefficient_eq_median]
  exact median_erase _ _ _ _ _ _

theorem prepareMeasured_erase (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (prepareMeasured rows C H K service B m ω).erase=
      prepare rows C H K service.solver B m ω := by
  rw [prepare_eq_cached]
  have he (b : Bool) :
      (MeasuredTable.build (fun j => coefficient rows C H K service B m ω (b,j))).erase =
      CountTable.build (fun j => (queries rows C H K service.solver (b,j)).cachedMedian B m ω) := by
    rw [MeasuredTable.erase_build]
    congr 1
    funext j
    exact Prod.ext (coefficient_erase rows C H K service B m ω (b,j)).1
      (coefficient_erase rows C H K service B m ω (b,j)).2
  exact congrArg₂ CoefficientTable.mk (he true) (he false)

/-- Time hypotheses apply only to the actual concrete service requests. They
can be discharged from a serializer bound and the external SAT contract. -/
theorem prepareMeasured_time (B m bound : ℕ) (ω : Fin (2*m+1) → Ω)
    (hb : ∀ i, (service.run (baseRequest rows C i [])).time≤bound)
    (hc : ∀ i s seed pre, pre.length≤keySize n r →
      (service.run (cellRequest rows C H K i s seed pre)).time≤bound) :
    (prepareMeasured rows C H K service B m ω).oracleTime≤
      2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*bound := by
  have hi (i : CoefficientIndex r) :
      (coefficient rows C H K service B m ω i).oracleTime≤
      (2*m+1)*trialCallBound (keySize n r) B*bound := by
    rw [coefficient_eq_median]
    exact median_oracleTime _ _ _ _ _ _ bound (fun _ => hb i) (fun seed s pre hp => hc i s seed pre hp)
  have hg := MeasuredTable.build_time_le
    (fun j => coefficient rows C H K service B m ω (true,j)) (fun j => hi (true,j))
  have hd := MeasuredTable.build_time_le
    (fun j => coefficient rows C H K service B m ω (false,j)) (fun j => hi (false,j))
  change _+_≤_
  calc
    _ ≤ _+_ := Nat.add_le_add hg hd
    _ = _ := by ring

/-- The computed output uses the measured cache once, then the existing exact
endpoint acquisition and single-pass repair. Postprocessing makes no SAT calls. -/
def output (shape : Bool) (a b c d : ℕ)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) : RationalOutput.LinearRepair.Output r :=
  let T := (prepareMeasured rows C H K service (rationalCellBudget a b)
    (rationalRepetitionBudget (2*(r+1)) c d) ω).erase
  let result := RationalOutput.LinearRepair.fromCache shape rows C T
  ⟨T,⟨result.values.toArray,by simp [result,RationalOutput.LinearRepair.fromCache_length]⟩,result.report⟩

theorem output_eq (shape : Bool) (a b c d : ℕ)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) :
    output rows C H K service shape a b c d ω=
      RationalOutput.LinearRepair.prepare shape rows C H K service.solver a b c d ω := by
  simp only [output,prepareMeasured_erase,RationalOutput.LinearRepair.prepare,prepareRational]

end QecReliability.OracleCost.QuantumService
