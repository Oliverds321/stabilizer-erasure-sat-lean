import TensorCountingTrace
import QecReliability.CachedEvaluator

/-! Identification of operational tensor trials from primitive query answers.
The primitive agreement is required only for prefixes the evaluator can read. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.CountingTrace
open OracleCost OracleCost.WholeWrapperCandidate PrefixEnumeration

theorem enumerate_congr_on (q : ℕ) (a b : List Bool → Bool) (cap : ℕ)
    (h : ∀ pre, pre.length ≤ q → a pre = b pre) :
    enumerate q a cap = enumerate q b cap := by
  induction q generalizing a b cap with
  | zero =>
    have h0 := h [] (by simp)
    simp [enumerate, h0]
  | succ q ih =>
    have h0 := h [] (by simp)
    by_cases hc : cap = 0
    · simp [enumerate, hc]
    · cases hb : b [] with
      | false => simp [enumerate, hc, h0, hb]
      | true =>
        have hl := ih (fun p => a (false::p)) (fun p => b (false::p)) cap
          (fun p hp => h (false::p) (by simp; omega))
        have hr := ih (fun p => a (true::p)) (fun p => b (true::p))
          (cap-(enumerate q (fun p => b (false::p)) cap).1)
          (fun p hp => h (true::p) (by simp; omega))
        simp only [enumerate, hc, ↓reduceIte, h0, hb]
        rw [hl, hr]

theorem cell_record_eq (q B : ℕ) (ext : External) (s : Config) (scale : ℕ)
    (answer : List Bool → Bool)
    (h : ∀ pre, pre.length ≤ q → (cellOracle ext s scale pre).value = answer pre) :
    ((cellResult q B ext s scale).count, (cellResult q B ext s scale).calls) =
      enumerate q answer (4*B+1) := by
  unfold cellResult
  rw [PrefixMachine.control_eq]
  simp only [List.nil_append]
  have he := PrefixControl.erase q (fun p => (cellOracle ext s scale p).value)
    (fun p => (cellOracle ext s scale p).time) (4*B+1)
  rw [he.1, he.2]
  exact enumerate_congr_on q _ answer _ h

theorem trial_eq_cached {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}
    (D : DecisionQueries e H S) (B : ℕ) (seed : Ω)
    (ext : External) (s : Config) (rep : ℕ)
    (hbase : (ext.sat (ext.compileQuery (baseKey s rep)).bits).value = D.base.answer [])
    (hcell : ∀ scale : Fin (q+1), ∀ pre, pre.length ≤ q →
      (cellOracle ext (trialAnchor s rep) scale.val pre).value = (D.cell scale seed).answer pre) :
    operationalTrial q B ext s rep = D.cachedTrial B seed := by
  have ht : cellEntries q B ext (trialAnchor s rep) (List.range (q+1)) =
      (CountTable.build (fun scale => enumerate q (D.cell scale seed).answer (4*B+1))).entries := by
    apply List.ext_getElem
    · simp [cellEntries, CountTable.build]
    · intro i hi hi'
      simp only [cellEntries, List.getElem_map, List.getElem_range,
        CountTable.build, List.getElem_ofFn]
      have hiq : i < q+1 := by simpa [cellEntries] using hi
      exact cell_record_eq q B ext (trialAnchor s rep) i
        (D.cell ⟨i,hiq⟩ seed).answer (hcell ⟨i,hiq⟩)
  unfold operationalTrial DecisionQueries.cachedTrial
  rw [hbase]
  cases hb : D.base.answer [] with
  | false => simp [hb]
  | true =>
    simp only [hb, ↓reduceIte]
    rw [cellCallSum_entries, ht]
    exact Prod.ext (ScaleSelection.select_eq B _) rfl

theorem coefficient_eq_cached {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}
    (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2*m+1) → Ω)
    (ext : External) (s : Config)
    (hbase : ∀ rep : Fin (2*m+1),
      (ext.sat (ext.compileQuery (baseKey s rep.val)).bits).value = D.base.answer [])
    (hcell : ∀ rep : Fin (2*m+1), ∀ scale : Fin (q+1), ∀ pre, pre.length ≤ q →
      (cellOracle ext (trialAnchor s rep.val) scale.val pre).value =
        (D.cell scale (ω rep)).answer pre) :
    operationalCoefficient q B m ext s = D.cachedMedian B m ω := by
  have hp : ∀ rep : Fin (2*m+1),
      operationalTrial q B ext s rep.val = D.cachedTrial B (ω rep) :=
    fun rep => trial_eq_cached D B (ω rep) ext s rep.val (hbase rep) (hcell rep)
  have he : repetitionEntries q B ext s (List.range (2*m+1)) =
      (CountTable.build (fun rep : Fin (2*m+1) => D.cachedTrial B (ω rep))).entries := by
    rw [repetitionEntries_ofFn]
    unfold CountTable.build
    congr 1
    exact funext hp
  have hv : (fun rep : Fin (2*m+1) => (operationalTrial q B ext s rep.val).1) =
      (fun rep => (D.cachedTrial B (ω rep)).1) :=
    funext (fun rep => congrArg Prod.fst (hp rep))
  unfold operationalCoefficient DecisionQueries.cachedMedian
  rw [hv, MedianSort.median_eq]
  apply Prod.ext
  · simp only [CountTable.get_build]
  · unfold repetitionCalls
    rw [he]
    rfl

end QecReliability.TensorMachine.CountingTrace
