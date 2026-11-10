import OracleCost.CachedControl

/-! Sequential repetition and coefficient batches for the same cached values.
Only callback time is certified here. Sorting, allocation and local arithmetic
remain visible integration obligations; no total-time theorem is inferred.
-/
namespace QecReliability.OracleCost.CachedControl
open scoped BigOperators
open PrefixEnumeration

structure MeasuredTable (n : ℕ) where
  entries : List TrialResult
  length_eq : entries.length=n

namespace MeasuredTable
def get {n : ℕ} (T : MeasuredTable n) (i : Fin n) : TrialResult :=
  T.entries.get ⟨i.val,by rw [T.length_eq]; exact i.isLt⟩
def build {n : ℕ} (f : Fin n → TrialResult) : MeasuredTable n :=
  ⟨List.ofFn f,List.length_ofFn⟩
def erase {n : ℕ} (T : MeasuredTable n) : CountTable n :=
  ⟨T.entries.map (fun x => (x.estimate,x.calls)),by simp [T.length_eq]⟩
def oracleTime {n : ℕ} (T : MeasuredTable n) : ℕ :=
  (T.entries.map TrialResult.oracleTime).sum
def prefixVisits {n : ℕ} (T : MeasuredTable n) : ℕ :=
  (T.entries.map TrialResult.prefixVisits).sum

@[simp] theorem get_build {n : ℕ} (f : Fin n → TrialResult) (i : Fin n) :
    (build f).get i=f i := by simp [get,build]
@[simp] theorem erase_build {n : ℕ} (f : Fin n → TrialResult) :
    (build f).erase=CountTable.build (fun i => ((f i).estimate,(f i).calls)) := by
  simp [erase,build,CountTable.build,List.map_ofFn,Function.comp_def]
@[simp] theorem oracleTime_build {n : ℕ} (f : Fin n → TrialResult) :
    (build f).oracleTime=∑ i, (f i).oracleTime := by
  simp [oracleTime,build,List.map_ofFn,List.sum_ofFn]

theorem build_time_le {n bound : ℕ} (f : Fin n → TrialResult)
    (h : ∀ i, (f i).oracleTime≤bound) : (build f).oracleTime≤n*bound := by
  rw [oracleTime_build]
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)
end MeasuredTable

variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

def median (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2*m+1) → Ω)
    (baseCharge : Ω → ℕ) (charge : Ω → Fin (q+1) → List Bool → ℕ) : TrialResult :=
  let trials := MeasuredTable.build (fun i => trial D B (ω i) (baseCharge (ω i)) (charge (ω i)))
  let values := trials.erase
  ⟨oddNatMedian (fun i => (values.get i).1),values.calls,trials.oracleTime,trials.prefixVisits⟩

theorem trial_table_erase (D : DecisionQueries e H S) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (baseCharge : Ω → ℕ)
    (charge : Ω → Fin (q+1) → List Bool → ℕ) :
    (MeasuredTable.build (fun i => trial D B (ω i) (baseCharge (ω i)) (charge (ω i)))).erase=
      CountTable.build (fun i => D.cachedTrial B (ω i)) := by
  rw [MeasuredTable.erase_build]
  congr 1
  funext i
  exact Prod.ext (trial_erase _ _ _ _ _).1 (trial_erase _ _ _ _ _).2

theorem median_erase (D : DecisionQueries e H S) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (baseCharge : Ω → ℕ)
    (charge : Ω → Fin (q+1) → List Bool → ℕ) :
    (median D B m ω baseCharge charge).estimate=(D.cachedMedian B m ω).1 ∧
    (median D B m ω baseCharge charge).calls=(D.cachedMedian B m ω).2 := by
  simp only [median,DecisionQueries.cachedMedian,trial_table_erase]
  exact ⟨trivial, trivial⟩

theorem median_oracleTime (D : DecisionQueries e H S) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (baseCharge : Ω → ℕ)
    (charge : Ω → Fin (q+1) → List Bool → ℕ) (bound : ℕ)
    (hbase : ∀ seed, baseCharge seed≤bound)
    (hcell : ∀ seed s pre, pre.length≤q → charge seed s pre≤bound) :
    (median D B m ω baseCharge charge).oracleTime≤
      (2*m+1)*trialCallBound q B*bound := by
  have h := MeasuredTable.build_time_le
    (fun i => trial D B (ω i) (baseCharge (ω i)) (charge (ω i)))
    (fun i => trial_linear_time_bound D B (ω i) _ _ bound (hbase _) (hcell _))
  simpa only [median,Nat.mul_assoc] using h

end QecReliability.OracleCost.CachedControl
