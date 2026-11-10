import QecReliability.PrefixEnumeration
import QecReliability.ConfidenceParameters

/-! Deriving the exact capped trial interface from prefix DECISION only.
An explicit key-to-bit equivalence carries no circuit-size or encoding-cost guarantee. -/

namespace QecReliability
open scoped BigOperators
open PrefixEnumeration

theorem encoded_modelCount {A : Type*} {q : ℕ} (e : A ≃ BitModels q) (S : Finset A) :
    modelCount (fun a => e.symm a ∈ S) = S.card := by
  classical
  have he : models (fun a => e.symm a ∈ S) = S.map e.toEmbedding := by
    ext a
    simp [models]
  rw [modelCount, he, Finset.card_map]

theorem encoded_card_bound {A : Type*} {q : ℕ} (e : A ≃ BitModels q) (S : Finset A) :
    S.card ≤ 2 ^ q := by
  rw [← encoded_modelCount e S]
  exact modelCount_bound _

/-- Base and cell predicates are decided under prefixes. No counting or probability guarantee is a field. -/
structure DecisionQueries {Ω A : Type*} [Fintype Ω] {q : ℕ}
    (e : A ≃ BitModels q) (H : HashStages Ω A q) (S : Finset A) where
  base : ExactDecision (fun a => e.symm a ∈ S)
  cell : ∀ (r : Fin (q + 1)) (ω : Ω),
    ExactDecision (fun a => e.symm a ∈ S ∧ H.hash r ω (e.symm a) = zeroCell r.val)

namespace DecisionQueries
variable {Ω A : Type*} [Fintype Ω] {q : ℕ}
    {e : A ≃ BitModels q} {H : HashStages Ω A q} {S : Finset A}

theorem cell_modelCount (_D : DecisionQueries e H S) (r : Fin (q + 1)) (ω : Ω) :
    modelCount (fun a => e.symm a ∈ S ∧ H.hash r ω (e.symm a) = zeroCell r.val) =
      H.cellCard S r ω := by
  classical
  have he : (fun a => e.symm a ∈ S ∧ H.hash r ω (e.symm a) = zeroCell r.val) =
      (fun a => e.symm a ∈ S.filter (fun z => H.hash r ω z = zeroCell r.val)) := by
    funext a
    simp
  rw [he, encoded_modelCount]
  rfl

def toTrialOracle (D : DecisionQueries e H S) : ExactTrialOracle H S where
  nonempty := D.base.answer []
  nonempty_spec := by
    rw [D.base.root]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨e.symm a, ha⟩
    · rintro ⟨a, ha⟩; exact ⟨e a, by simpa using ha⟩
  capped cap r ω := (enumerate q (D.cell r ω).answer cap).1
  capped_spec cap r ω := by
    rw [(enumerate_spec (D.cell r ω) cap).1, D.cell_modelCount, Nat.min_comm]

theorem capped_decision_calls (D : DecisionQueries e H S) (cap : ℕ)
    (r : Fin (q + 1)) (ω : Ω) :
    (enumerate q (D.cell r ω).answer cap).2 ≤ 1 + 2 * q * min cap (H.cellCard S r ω) := by
  simpa only [D.cell_modelCount] using (enumerate_spec (D.cell r ω) cap).2

/-- Conservative count for evaluating the initial emptiness query and EVERY scale's capped cell. -/
def allCellsCalls (D : DecisionQueries e H S) (cap : ℕ) (ω : Ω) : ℕ :=
  1 + ∑ r : Fin (q + 1), (enumerate q (D.cell r ω).answer cap).2

theorem allCellsCalls_bound (D : DecisionQueries e H S) (cap : ℕ) (ω : Ω) :
    D.allCellsCalls cap ω ≤ 1 + (q + 1) * (1 + 2 * q * cap) := by
  unfold allCellsCalls
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _r : Fin (q + 1), (1 + 2 * q * cap) := by
      apply Finset.sum_le_sum
      intro r _
      exact (D.capped_decision_calls cap r ω).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.min_le_left cap _)) 1)
    _ = _ := by simp

end DecisionQueries

/-- Global confidence now assumes exact PREFIX DECISION, rather than exact capped counting. -/
theorem confidence_from_decisions {I Ω A : Type*} [Fintype I] [Fintype Ω] {q : ℕ}
    (e : A ≃ BitModels q) (H : HashStages Ω A q) (S : I → Finset A)
    (D : ∀ i, DecisionQueries e H (S i))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card I) δ hδ)).prob
      (fun ω => ∀ i,
        |ExactTrialOracle.amplified (fun i => (D i).toTrialOracle) (cellBudget ε)
            (repetitionBudget (Fintype.card I) δ hδ) ω i - ((S i).card : ℝ)| ≤
          ε * ((S i).card : ℝ)) :=
  automatic_count_confidence (fun i => (D i).toTrialOracle)
    (fun i => encoded_card_bound e (S i)) hε hε1 hδ

end QecReliability
