import QecReliability.CachedEvaluator
import Mathlib.Data.Nat.Size

/-! Binary payload bounds for materialized tables. These do not bound the Lean
runtime heap, recursion/sorting workspace, seed representation, or SAT solver. -/
namespace QecReliability
open scoped BigOperators
open PrefixEnumeration

def CountTable.payloadBits {n : ℕ} (T : CountTable n) : ℕ :=
  (T.entries.map (fun p => p.1.size + p.2.size)).sum

theorem CountTable.payloadBits_build {n : ℕ} (f : Fin n → ℕ × ℕ) :
    (CountTable.build f).payloadBits = ∑ i, ((f i).1.size + (f i).2.size) := by
  simp [CountTable.payloadBits, CountTable.build, List.map_ofFn, List.sum_ofFn]

theorem CountTable.payloadBits_le {n U V : ℕ} (f : Fin n → ℕ × ℕ)
    (h : ∀ i, (f i).1 ≤ U ∧ (f i).2 ≤ V) :
    (CountTable.build f).payloadBits ≤ n * (U.size + V.size) := by
  rw [CountTable.payloadBits_build]
  calc
    _ ≤ ∑ _ : Fin n, (U.size + V.size) := Finset.sum_le_sum (fun i _ =>
      Nat.add_le_add (Nat.size_le_size (h i).1) (Nat.size_le_size (h i).2))
    _ = _ := by simp

def trialCallBound (q B : ℕ) : ℕ := 1 + (q + 1) * (1 + 2 * q * (4 * B + 1))
def trialValueBound (q B : ℕ) : ℕ := 2 ^ q * (4 * B + 1)

theorem trialValueBound_size (q B : ℕ) : (trialValueBound q B).size ≤ q + (4 * B + 1).size := by
  apply Nat.size_le.mpr
  unfold trialValueBound
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (pow_pos (by decide) q)

theorem selectCached_le {q : ℕ} (B : ℕ) (T : CountTable (q + 1))
    (hT : ∀ i, (T.get i).1 ≤ 4 * B + 1) : selectCached B T ≤ trialValueBound q B := by
  dsimp only [selectCached]
  split
  · apply max_le
    · unfold trialValueBound
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
    · have hs := (Finset.univ.filter (fun s => (T.get s).1 ≤ 4 * B)).min'_mem ‹_›
      have hr : ((Finset.univ.filter (fun s => (T.get s).1 ≤ 4 * B)).min' ‹_›).val ≤ q := by omega
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hr) (hT _)
  · unfold trialValueBound
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))

namespace DecisionQueries
variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

theorem cell_entry_bounds (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) (s : Fin (q + 1)) :
    (enumerate q (D.cell s ω).answer (4 * B + 1)).1 ≤ 4 * B + 1 ∧
    (enumerate q (D.cell s ω).answer (4 * B + 1)).2 ≤ 1 + 2 * q * (4 * B + 1) := by
  refine ⟨?_, (D.capped_decision_calls _ s ω).trans (by gcongr; exact Nat.min_le_left _ _)⟩
  rw [(enumerate_spec (D.cell s ω) _).1]
  exact Nat.min_le_left _ _

theorem cell_table_payload (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    (CountTable.build (fun s => enumerate q (D.cell s ω).answer (4 * B + 1))).payloadBits ≤
      (q + 1) * ((4 * B + 1).size + (1 + 2 * q * (4 * B + 1)).size) :=
  CountTable.payloadBits_le _ (D.cell_entry_bounds B ω)

theorem cachedTrial_bounds (D : DecisionQueries e H S) (B : ℕ) (ω : Ω) :
    (D.cachedTrial B ω).1 ≤ trialValueBound q B ∧
    (D.cachedTrial B ω).2 ≤ trialCallBound q B := by
  refine ⟨?_, D.cachedTrial_calls B ω⟩
  dsimp only [cachedTrial]
  split
  · apply selectCached_le
    intro i
    simpa using (D.cell_entry_bounds B ω i).1
  · exact Nat.zero_le _

theorem trial_table_payload (D : DecisionQueries e H S) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) :
    (CountTable.build (fun i => D.cachedTrial B (ω i))).payloadBits ≤
      (2 * m + 1) * (q + (4 * B + 1).size + (trialCallBound q B).size) := by
  have h := CountTable.payloadBits_le (fun i => D.cachedTrial B (ω i))
    (fun i => D.cachedTrial_bounds B (ω i))
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (trialValueBound_size q B) _))

theorem cachedMedian_bounds (D : DecisionQueries e H S) (B m : ℕ)
    (ω : Fin (2 * m + 1) → Ω) :
    (D.cachedMedian B m ω).1 ≤ trialValueBound q B ∧
    (D.cachedMedian B m ω).2 ≤ (2 * m + 1) * trialCallBound q B := by
  refine ⟨?_, D.cachedMedian_calls B m ω⟩
  simp only [cachedMedian, oddNatMedian, CountTable.get_build]
  exact (D.cachedTrial_bounds B _).1

end DecisionQueries

namespace SharedCircuit.ConcreteQuantum
open LatentEncoding

def CoefficientTable.payloadBits {r : ℕ} (T : CoefficientTable r) : ℕ :=
  T.good.payloadBits + T.bad.payloadBits

theorem prepare_entry_count {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    (prepare rows C H K solver B m ω).good.entries.length +
      (prepare rows C H K solver B m ω).bad.entries.length = 2 * (r + 1) := by
  rw [CountTable.length_eq, CountTable.length_eq]
  omega

theorem prepare_payload {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2 * m + 1) → Ω) :
    (prepare rows C H K solver B m ω).payloadBits ≤
      2 * (r + 1) * (keySize n r + (4 * B + 1).size +
        ((2 * m + 1) * trialCallBound (keySize n r) B).size) := by
  have h (side : Bool) := CountTable.payloadBits_le
    (fun j => (queries rows C H K solver (side, j)).cachedMedian B m ω)
    (fun j => (queries rows C H K solver (side, j)).cachedMedian_bounds B m ω)
  rw [prepare_eq_cached]
  dsimp only [CoefficientTable.payloadBits]
  have hv := trialValueBound_size (keySize n r) B
  have hh := Nat.add_le_add (h true) (h false)
  nlinarith

end SharedCircuit.ConcreteQuantum
end QecReliability
