import OracleCost.PrefixControl
import QecReliability.CachedStorage

/-! Ghost cost interpretation of the actual all-scales cached trial. The same
cell list supplies selection and the measured call totals. The original SAT
cache, rather than a first-stopping-scale implementation, is the value target.
Local table construction, lookup and median costs are still separate obligations.
-/
namespace QecReliability.OracleCost.CachedControl
open scoped BigOperators
open PrefixEnumeration

structure TrialResult where
  estimate : ℕ
  calls : ℕ
  oracleTime : ℕ
  prefixVisits : ℕ

variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

def cells (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (charge : Fin (q+1) → List Bool → ℕ) : List PrefixControl.Result :=
  List.ofFn (fun s => PrefixControl.run q (D.cell s ω).answer (charge s) (4*B+1))

def table (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (charge : Fin (q+1) → List Bool → ℕ) : CountTable (q+1) :=
  ⟨(cells D B ω charge).map (fun x => (x.count,x.calls)),by simp [cells]⟩

theorem table_eq (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (charge : Fin (q+1) → List Bool → ℕ) :
    table D B ω charge=CountTable.build (fun s => enumerate q (D.cell s ω).answer (4*B+1)) := by
  have h : (cells D B ω charge).map (fun x => (x.count,x.calls))=
      List.ofFn (fun s => enumerate q (D.cell s ω).answer (4*B+1)) := by
    simp only [cells,List.map_ofFn]
    congr 1
    funext s
    exact Prod.ext (PrefixControl.erase _ _ _ _).1 (PrefixControl.erase _ _ _ _).2
  unfold table CountTable.build
  simp only [h]

def trial (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) : TrialResult :=
  if D.base.answer [] then
    let entries := cells D B ω charge
    let cache : CountTable (q+1) :=
      ⟨entries.map (fun x => (x.count,x.calls)),by simp [entries,cells]⟩
    ⟨selectCached B cache,1+cache.calls,
      baseCharge+(entries.map PrefixControl.Result.oracleTime).sum,
      (entries.map PrefixControl.Result.visits).sum⟩
  else ⟨0,1,baseCharge,0⟩

theorem trial_erase (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) :
    (trial D B ω baseCharge charge).estimate=(D.cachedTrial B ω).1 ∧
    (trial D B ω baseCharge charge).calls=(D.cachedTrial B ω).2 := by
  cases hd : D.base.answer [] with
  | false => simp [trial,DecisionQueries.cachedTrial,hd]
  | true =>
    simp only [trial,DecisionQueries.cachedTrial,hd,↓reduceIte]
    change selectCached B (table D B ω charge)=_ ∧ 1+(table D B ω charge).calls=_
    rw [table_eq]
    exact ⟨rfl,rfl⟩

theorem trial_calls_bound (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) :
    (trial D B ω baseCharge charge).calls≤trialCallBound q B := by
  rw [(trial_erase D B ω baseCharge charge).2]
  exact D.cachedTrial_calls B ω

theorem trial_oracleTime (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) (bound : ℕ)
    (hbase : baseCharge≤bound)
    (hcell : ∀ s pre, pre.length≤q → charge s pre≤bound) :
    (trial D B ω baseCharge charge).oracleTime≤
      (trial D B ω baseCharge charge).calls*bound := by
  cases hd : D.base.answer [] with
  | false => simpa [trial,hd] using hbase
  | true =>
    have hs : (∑ s : Fin (q+1),
        (PrefixControl.run q (D.cell s ω).answer (charge s) (4*B+1)).oracleTime)≤
        (∑ s : Fin (q+1), (PrefixControl.run q (D.cell s ω).answer (charge s) (4*B+1)).calls)*bound := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun s _ => PrefixControl.oracleTime_le _ _ _ _ _ (hcell s))
    simp only [trial,hd,↓reduceIte,CountTable.calls,cells,List.map_ofFn,
      List.sum_ofFn,Function.comp_apply]
    nlinarith

theorem trial_linear_time_bound (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) (bound : ℕ)
    (hbase : baseCharge≤bound)
    (hcell : ∀ s pre, pre.length≤q → charge s pre≤bound) :
    (trial D B ω baseCharge charge).oracleTime≤trialCallBound q B*bound :=
  (trial_oracleTime D B ω baseCharge charge bound hbase hcell).trans
    (Nat.mul_le_mul_right _ (trial_calls_bound D B ω baseCharge charge))

theorem trial_visits_bound (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (baseCharge : ℕ) (charge : Fin (q+1) → List Bool → ℕ) :
    (trial D B ω baseCharge charge).prefixVisits≤
      2*(trial D B ω baseCharge charge).calls+(q+1) := by
  cases hd : D.base.answer [] with
  | false => simp [trial,hd]
  | true =>
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (s : Fin (q+1)) _ =>
      PrefixControl.visits_le q (D.cell s ω).answer (charge s) (4*B+1))
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
    simp only [trial,hd,↓reduceIte,CountTable.calls,cells,List.map_ofFn,
      List.sum_ofFn,Function.comp_apply]
    omega

end QecReliability.OracleCost.CachedControl
