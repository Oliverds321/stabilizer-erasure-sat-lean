import QecReliability.ConcreteQuantumConfidence

/-! Materialized cell/trial tables: the returned decision count accounts for the
same evaluator whose value is proved equal to the confidence theorem's estimate. -/
namespace QecReliability
open scoped BigOperators
open PrefixEnumeration

structure CountTable (n : ℕ) where
  entries : List (ℕ × ℕ)
  length_eq : entries.length = n

namespace CountTable

def get {n : ℕ} (T : CountTable n) (i : Fin n) : ℕ × ℕ :=
  T.entries.get ⟨i.val, by rw [T.length_eq]; exact i.isLt⟩

def build {n : ℕ} (f : Fin n → ℕ × ℕ) : CountTable n := ⟨List.ofFn f, List.length_ofFn⟩

@[simp] theorem get_build {n : ℕ} (f : Fin n → ℕ × ℕ) (i : Fin n) : (build f).get i = f i := by
  simp [get, build]

def calls {n : ℕ} (T : CountTable n) : ℕ := (T.entries.map Prod.snd).sum

@[simp] theorem calls_build {n : ℕ} (f : Fin n → ℕ × ℕ) : (build f).calls = ∑ i, (f i).2 := by
  simp [calls, build, List.map_ofFn, List.sum_ofFn]

theorem calls_build_le {n K : ℕ} (f : Fin n → ℕ × ℕ) (h : ∀ i, (f i).2 ≤ K) :
    (build f).calls ≤ n * K := by
  rw [calls_build]
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)

end CountTable

def selectCached {q : ℕ} (B : ℕ) (T : CountTable (q + 1)) : ℕ :=
  let accepted := Finset.univ.filter (fun s => (T.get s).1 ≤ 4 * B)
  if h : accepted.Nonempty then
    let s := accepted.min' h
    max 1 (2 ^ s.val * (T.get s).1)
  else 1

namespace DecisionQueries
variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

/-- The Boolean base call is made once. Each capped cell is materialized once,
then selection reads the stored count. The second component counts those calls. -/
def cachedTrial (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) : ℕ × ℕ :=
  let nonempty := D.base.answer []
  if nonempty then
    let table := CountTable.build (fun s => enumerate q (D.cell s ω).answer (4 * B + 1))
    (selectCached B table, 1 + table.calls)
  else (0, 1)

theorem cachedTrial_value (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    (D.cachedTrial B ω).1 = D.toTrialOracle.trial B ω := by
  unfold cachedTrial ExactTrialOracle.trial
  simp only [toTrialOracle]
  split <;> simp only
  simp only [selectCached, CountTable.get_build, ExactTrialOracle.accepted]

theorem cachedTrial_calls (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    (D.cachedTrial B ω).2 ≤ 1 + (q + 1) * (1 + 2 * q * (4 * B + 1)) := by
  cases hn : D.base.answer []
  · simp [cachedTrial, hn]
  · simp only [cachedTrial, hn, ↓reduceIte]
    apply Nat.add_le_add_left
    apply CountTable.calls_build_le
    intro s
    exact (D.capped_decision_calls (4 * B + 1) s ω).trans
      (by gcongr; exact Nat.min_le_left _ _)

theorem cachedTrial_empty_calls (D : DecisionQueries e H S) (B : ℕ) (ω : Ω)
    (h : D.base.answer [] = false) : D.cachedTrial B ω = (0, 1) := by simp [cachedTrial, h]

end DecisionQueries

def oddNatMedian {m : ℕ} (X : Fin (2 * m + 1) → ℕ) : ℕ := X (Tuple.sort X ⟨m, by omega⟩)

theorem oddNatMedian_cast {m : ℕ} (X : Fin (2 * m + 1) → ℕ) :
    (oddNatMedian X : ℝ) = oddMedian (fun i => (X i : ℝ)) := by
  have hmono : Monotone ((fun i => (X i : ℝ)) ∘ Tuple.sort X) := by
    intro i j hij
    change (X (Tuple.sort X i) : ℝ) ≤ (X (Tuple.sort X j) : ℝ)
    exact_mod_cast (show X (Tuple.sort X i) ≤ X (Tuple.sort X j) from Tuple.monotone_sort X hij)
  have he := (Tuple.comp_sort_eq_comp_iff_monotone
    (f := fun i => (X i : ℝ)) (σ := Tuple.sort X)).mpr hmono
  exact congrFun he ⟨m, by omega⟩

namespace DecisionQueries
variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

/-- Duplicate trial values are preserved in a materialized table; the natural-number
median and all later lookups perform no decision-oracle calls. -/
def cachedMedian (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) : ℕ × ℕ :=
  let table := CountTable.build (fun i => D.cachedTrial B (ω i))
  (oddNatMedian (fun i => (table.get i).1), table.calls)

theorem cachedMedian_value (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    ((D.cachedMedian B m ω).1 : ℝ) = medianEstimate (fun seed => (D.toTrialOracle.trial B seed : ℝ)) ω := by
  simp only [cachedMedian, CountTable.get_build, cachedTrial_value, oddNatMedian_cast]
  rfl

theorem cachedMedian_calls (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    (D.cachedMedian B m ω).2 ≤ (2 * m + 1) * (1 + (q + 1) * (1 + 2 * q * (4 * B + 1))) := by
  exact CountTable.calls_build_le _ (fun _ => D.cachedTrial_calls B _)

end DecisionQueries

/- Executable caching depends only on Boolean answer callbacks. The model set
and its correctness proofs remain in `DecisionQueries`, outside this interface. -/
namespace CachedAnswers

def trial {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q + 1) → Ω → List Bool → Bool)
    (B : ℕ) (ω : Ω) : ℕ × ℕ :=
  let nonempty := baseAnswer []
  if nonempty then
    let table := CountTable.build (fun s => enumerate q (cellAnswer s ω) (4 * B + 1))
    (selectCached B table, 1 + table.calls)
  else (0, 1)

def median {Ω : Type*} {q : ℕ}
    (baseAnswer : List Bool → Bool)
    (cellAnswer : Fin (q + 1) → Ω → List Bool → Bool)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) : ℕ × ℕ :=
  let table := CountTable.build (fun i => trial baseAnswer cellAnswer B (ω i))
  (oddNatMedian (fun i => (table.get i).1), table.calls)

theorem trial_eq {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}
    (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    trial D.base.answer (fun s seed => (D.cell s seed).answer) B ω =
      D.cachedTrial B ω := rfl

theorem median_eq {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}
    (D : DecisionQueries e H S) (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    median D.base.answer (fun s seed => (D.cell s seed).answer) B m ω =
      D.cachedMedian B m ω := rfl

end CachedAnswers

namespace SharedCircuit.ConcreteQuantum
open LatentEncoding

structure CoefficientTable (r : ℕ) where
  good : CountTable (r + 1)
  bad : CountTable (r + 1)

def CoefficientTable.calls {r : ℕ} (T : CoefficientTable r) : ℕ := T.good.calls + T.bad.calls

def prepare {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) : CoefficientTable r :=
  ⟨CountTable.build (fun j =>
      let D := queries rows C H K solver (true, j)
      CachedAnswers.median D.base.answer (fun s seed => (D.cell s seed).answer) B m ω),
   CountTable.build (fun j =>
      let D := queries rows C H K solver (false, j)
      CachedAnswers.median D.base.answer (fun s seed => (D.cell s seed).answer) B m ω)⟩

theorem prepare_eq_cached {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    prepare rows C H K solver B m ω =
      ⟨CountTable.build (fun j => (queries rows C H K solver (true, j)).cachedMedian B m ω),
       CountTable.build (fun j => (queries rows C H K solver (false, j)).cachedMedian B m ω)⟩ := rfl

theorem prepare_calls {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    (prepare rows C H K solver B m ω).calls ≤
      2 * (r + 1) * (2 * m + 1) *
        (1 + (keySize n r + 1) * (1 + 2 * keySize n r * (4 * B + 1))) := by
  have hg := CountTable.calls_build_le
    (fun j => (queries rows C H K solver (true, j)).cachedMedian B m ω)
    (fun j => (queries rows C H K solver (true, j)).cachedMedian_calls B m ω)
  have hb := CountTable.calls_build_le
    (fun j => (queries rows C H K solver (false, j)).cachedMedian B m ω)
    (fun j => (queries rows C H K solver (false, j)).cachedMedian_calls B m ω)
  change _ + _ ≤ _
  calc
    _ ≤ _ + _ := Nat.add_le_add hg hb
    _ = _ := by ring

noncomputable def CoefficientTable.curve {r : ℕ} (T : CoefficientTable r) : ℝ → ℝ :=
  bernsteinCurve r (fun j => ((T.good.get j).1 : ℝ) /
    (((T.good.get j).1 : ℝ) + ((T.bad.get j).1 : ℝ)))

theorem prepare_values {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (ε δ : ℝ) (hδ : 0 < δ)
    (ω : Fin (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) → Ω)
    (j : Fin (r + 1)) :
    (((prepare rows C H K solver (cellBudget (ε / 3))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω).good.get j).1 : ℝ) =
        estimates rows C H K solver ε δ hδ ω (true, j) ∧
    (((prepare rows C H K solver (cellBudget (ε / 3))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω).bad.get j).1 : ℝ) =
        estimates rows C H K solver ε δ hδ ω (false, j) := by
  constructor <;> simp only [prepare_eq_cached, CountTable.get_build, DecisionQueries.cachedMedian_value,
    estimates, ExactTrialOracle.amplified]

/-- Confidence and cost refer to the same materialized coefficient table.
Curve evaluation after preparation invokes no decision callback. -/
theorem cached_curve_confidence {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let T := prepare rows C H K solver (cellBudget (ε / 3))
          (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω
        T.calls ≤ 2 * (r + 1) *
          (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) *
          (1 + (keySize n r + 1) * (1 + 2 * keySize n r * (4 * cellBudget (ε / 3) + 1))) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p) (T.curve p) ∧
          0 ≤ T.curve p ∧ T.curve p ≤ 1) := by
  apply (curve_confidence rows hS C H K solver hε hε1 hδ).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  refine ⟨prepare_calls rows C H K solver _ _ ω, ?_⟩
  intro p hp
  change RelPair ε _ (bernsteinCurve r _ p) ∧ _
  simp only [CoefficientTable.curve]
  simp_rw [(prepare_values rows C H K solver ε δ hδ ω _).1,
    (prepare_values rows C H K solver ε δ hδ ω _).2]
  exact hω p hp

end SharedCircuit.ConcreteQuantum

end QecReliability
