import TensorQueryBoundary

/-! Total calls and measured SAT service time of the actual tensor counting
schedule. Every coefficient is evaluated once on each side. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorMachine.CountingTrace
open OracleCost OracleCost.WholeWrapperCandidate

private theorem sum_map_le_mul {α : Type*} (xs : List α) (f g : α → ℕ) (R : ℕ)
    (h : ∀ x∈xs, f x≤g x*R) :
    (xs.map f).sum≤(xs.map g).sum*R := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    nlinarith

variable (q r B m : ℕ) (ext : External) (R : ℕ)
  (hcharge : ∀ key, ValidKey q r m key → (ext.sat (ext.compileQuery key).bits).time≤R)

include hcharge in
theorem trial_time_le (s : Config) (hj : s.coefficient<r+1)
    (rep : ℕ) (hrep : rep<2*m+1) :
    operationalTrialTime q B ext s rep≤(operationalTrial q B ext s rep).2*R := by
  have hb := hcharge (baseKey s rep) ⟨hj,hrep⟩
  have hcell : ∀ scale∈List.range (q+1),
      (cellResult q B ext (trialAnchor s rep) scale).oracleTime≤
        (cellResult q B ext (trialAnchor s rep) scale).calls*R := by
    intro scale hscale
    unfold cellResult
    rw [PrefixMachine.control_eq]
    apply PrefixControl.oracleTime_le
    intro pre hpre
    change (ext.sat (ext.compileQuery
      (cellKey { trialAnchor s rep with scale := scale } ([]++pre))).bits).time≤R
    rw [List.nil_append]
    exact hcharge
      (cellKey { trialAnchor s rep with scale := scale } pre)
      ⟨hj,hrep,List.mem_range.mp hscale,hpre⟩
  have hc := sum_map_le_mul (List.range (q+1))
    (fun scale => (cellResult q B ext (trialAnchor s rep) scale).oracleTime)
    (fun scale => (cellResult q B ext (trialAnchor s rep) scale).calls) R hcell
  change cellTimeSum q B ext (trialAnchor s rep) (List.range (q+1))≤
    cellCallSum q B ext (trialAnchor s rep) (List.range (q+1))*R at hc
  cases hvalue : (ext.sat (ext.compileQuery (baseKey s rep)).bits).value <;>
    simp only [operationalTrialTime,operationalTrial,hvalue,Bool.false_eq_true,
      if_false,if_true,↓reduceIte,Nat.add_zero,Nat.one_mul] <;> nlinarith

include hcharge in
theorem entry_time_le (side : Bool) (j : Fin (r+1)) :
    entryTime q r B m ext side j≤(entry q r B m ext side j).2*R := by
  have h := sum_map_le_mul (List.range (2*m+1))
    (operationalTrialTime q B ext { initial q r m with good := side,coefficient := j.val })
    (fun rep => (operationalTrial q B ext
      { initial q r m with good := side,coefficient := j.val } rep).2) R
    (fun rep hp => trial_time_le q r B m ext R hcharge _ j.isLt rep (List.mem_range.mp hp))
  simpa only [entryTime,entry,operationalCoefficient,repetitionTime,repetitionCalls,
    repetitionEntries,List.map_map,Function.comp_def] using h

include hcharge in
theorem side_time_le (side : Bool) (js : List (Fin (r+1))) :
    sideTime q r B m ext side js≤sideCalls q r B m ext side js*R := by
  have h := sum_map_le_mul js (entryTime q r B m ext side)
    (fun j => (entry q r B m ext side j).2) R
    (fun j _ => entry_time_le q r B m ext R hcharge side j)
  simpa only [sideTime,sideCalls,sideEntries,List.map_map,Function.comp_def] using h

end QecReliability.TensorMachine.CountingTrace

noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting SharedCircuit.LatentEncoding
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

theorem entry_calls_le (B : ℕ) (side : Bool) (j : Fin (slots ds-1+1)) :
    (CountingTrace.entry (keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) side j).2≤
        (2*m+1)*trialCallCap (keySize n ds.sum) B := by
  rw [entry_eq rows C H K m ω density spec B side j]
  exact DecisionQueries.cachedMedian_calls _ B m ω

theorem side_calls_le (B : ℕ) (side : Bool) (js : List (Fin (slots ds-1+1))) :
    CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) side js≤
        js.length*((2*m+1)*trialCallCap (keySize n ds.sum) B) := by
  induction js with
  | nil => simp [CountingTrace.sideCalls,CountingTrace.sideEntries]
  | cons j js ih =>
    have hj := entry_calls_le rows C H K m ω density spec B side j
    change (CountingTrace.entry (keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) side j).2+
      CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m
        (external rows C H K m ω density spec) side js≤_
    rw [List.length_cons]
    nlinarith

theorem total_calls_le (B : ℕ) :
    CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) true (List.finRange (slots ds-1+1))+
    CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) false (List.finRange (slots ds-1+1))≤
        2*slots ds*(2*m+1)*trialCallCap (keySize n ds.sum) B := by
  have ht := side_calls_le rows C H K m ω density spec B true (List.finRange (slots ds-1+1))
  have hf := side_calls_le rows C H K m ω density spec B false (List.finRange (slots ds-1+1))
  rw [List.length_finRange] at ht hf
  have he := slots_pred_succ ds
  nlinarith

theorem request_time_le (hT : Monotone T) (V R : ℕ)
    (hV : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key),
      (padRequest density (resolve rows C H K m ω key valid)).varCount≤V)
    (hR : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key),
      resource (padRequest density (resolve rows C H K m ω key valid))≤R)
    (key : RequestKey) (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    ((external rows C H K m ω density spec).sat
      ((external rows C H K m ω density spec).compileQuery key).bits).time≤Pt.eval R*T V := by
  rw [answer rows C H K m ω density spec key valid]
  exact (spec.request_bounds hT _ V R (hV key valid) (hR key valid)).1

/-- The actual initial counting trace, with explicit SAT-call and service-time
bounds. The common padded request caps are ordinary resource bounds, not
assumptions about the estimator or its returned cache. -/
theorem counting_budget (B : ℕ) (shape : Bool) (hT : Monotone T) (V R : ℕ)
    (hV : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key),
      (padRequest density (resolve rows C H K m ω key valid)).varCount≤V)
    (hR : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key),
      resource (padRequest density (resolve rows C H K m ω key valid))≤R) :
    ∃ final totals events,
      Trace (keySize n ds.sum) (slots ds-1) B m shape
        (external rows C H K m ω density spec) (initial (keySize n ds.sum) (slots ds-1) m)
        totals events final ∧
      final.pc=.endpointZero ∧ final.code=[] ∧
      final.goodTable=CountingTrace.sideEntries (keySize n ds.sum) (slots ds-1) B m
        (external rows C H K m ω density spec) true (List.finRange (slots ds-1+1)) ∧
      final.badTable=CountingTrace.sideEntries (keySize n ds.sum) (slots ds-1) B m
        (external rows C H K m ω density spec) false (List.finRange (slots ds-1+1)) ∧
      totals.calls≤2*slots ds*(2*m+1)*trialCallCap (keySize n ds.sum) B ∧
      totals.oracleTime≤totals.calls*(Pt.eval R*T V) ∧
      totals.endpointTime=0 ∧
      totals.dispatches≤8*totals.calls+2*slots ds*coefficientLocalBound (keySize n ds.sum) m+
        2*slots ds+3 := by
  obtain ⟨final,totals,events,htrace,hpc,hcode,hgood,hbad,hcalls,htime,hendpoint,hsteps⟩ :=
    CountingTrace.initial_to_tables_trace (keySize n ds.sum) (slots ds-1) B m shape
      (external rows C H K m ω density spec)
  have hc := total_calls_le rows C H K m ω density spec B
  have charge := request_time_le rows C H K m ω density spec hT V R hV hR
  have ht := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m
    (external rows C H K m ω density spec) (Pt.eval R*T V) charge true (List.finRange (slots ds-1+1))
  have hf := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m
    (external rows C H K m ω density spec) (Pt.eval R*T V) charge false (List.finRange (slots ds-1+1))
  rw [slots_pred_succ] at hsteps
  refine ⟨final,totals,events,htrace,hpc,hcode,hgood,hbad,?_,?_,hendpoint,hsteps⟩
  · rw [hcalls]; exact hc
  · rw [hcalls,htime]
    nlinarith

end QecReliability.TensorMachine.Boundary
