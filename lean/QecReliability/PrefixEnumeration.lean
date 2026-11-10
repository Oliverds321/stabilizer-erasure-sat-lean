import QecReliability.TargetScale
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Exact distinct-projection counting from a prefix decision oracle, with a
recursive implementation and explicit decision-call accounting. -/

namespace QecReliability
namespace PrefixEnumeration
open scoped BigOperators

noncomputable def models {q : ℕ} (P : BitModels q → Prop) : Finset (BitModels q) := by
  classical
  exact Finset.univ.filter P

noncomputable def modelCount {q : ℕ} (P : BitModels q → Prop) : ℕ := (models P).card

theorem modelCount_pos {q : ℕ} (P : BitModels q → Prop) : 0 < modelCount P ↔ ∃ a, P a := by
  classical
  simp [modelCount, models, Finset.card_pos, Finset.filter_nonempty_iff]

theorem modelCount_bound {q : ℕ} (P : BitModels q → Prop) : modelCount P ≤ 2 ^ q :=
  bitModels_card_bound (models P)

theorem modelCount_branch {q : ℕ} (P : BitModels (q + 1) → Prop) :
    modelCount P = modelCount (fun a => P (Fin.cons false a)) +
      modelCount (fun a => P (Fin.cons true a)) := by
  classical
  simp only [modelCount, models, Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (q + 1) => Bool)).sum_comp (fun a => if P a then 1 else 0),
    Fintype.sum_prod_type, Fintype.sum_bool]
  exact Nat.add_comm _ _

/-- Existential witnesses, if present in P, are never part of the counted assignment. -/
def PrefixSat {q : ℕ} (P : BitModels q → Prop) (pre : List Bool) : Prop :=
  ∃ a, P a ∧ pre <+: List.ofFn a

theorem prefixSat_nil {q : ℕ} (P : BitModels q → Prop) : PrefixSat P [] ↔ ∃ a, P a := by
  simp [PrefixSat]

theorem prefixSat_cons {q : ℕ} (P : BitModels (q + 1) → Prop) (b : Bool) (pre : List Bool) :
    PrefixSat P (b :: pre) ↔ PrefixSat (fun a => P (Fin.cons b a)) pre := by
  unfold PrefixSat
  rw [Fin.exists_fin_succ_pi]
  simp only [List.ofFn_cons, List.cons_prefix_cons]
  constructor
  · rintro ⟨b', a, hp, hbb, hpre⟩
    subst b'
    exact ⟨a, hp, hpre⟩
  · rintro ⟨a, hp, hpre⟩
    exact ⟨b, a, hp, rfl, hpre⟩

/-- The only semantic oracle assumption: exact satisfiability under each Boolean prefix. -/
structure ExactDecision {q : ℕ} (P : BitModels q → Prop) where
  answer : List Bool → Bool
  correct : ∀ pre, answer pre = true ↔ PrefixSat P pre

namespace ExactDecision
variable {q : ℕ} {P : BitModels q → Prop}

theorem root (D : ExactDecision P) : D.answer [] = true ↔ ∃ a, P a :=
  (D.correct []).trans (prefixSat_nil P)

def branch {q : ℕ} {P : BitModels (q + 1) → Prop} (D : ExactDecision P) (b : Bool) :
    ExactDecision (fun a => P (Fin.cons b a)) where
  answer pre := D.answer (b :: pre)
  correct pre := (D.correct (b :: pre)).trans (prefixSat_cons P b pre)

end ExactDecision

/-- Result is (distinct assignments counted, decision calls).
The right branch receives the unused cap; cap zero never queries the oracle. -/
def enumerate : (q : ℕ) → (List Bool → Bool) → ℕ → ℕ × ℕ
  | 0, answer, cap =>
      if cap = 0 then (0, 0) else if answer [] then (1, 1) else (0, 1)
  | q + 1, answer, cap =>
      if cap = 0 then (0, 0) else if answer [] then
        let left := enumerate q (fun pre => answer (false :: pre)) cap
        let right := enumerate q (fun pre => answer (true :: pre)) (cap - left.1)
        (left.1 + right.1, 1 + left.2 + right.2)
      else (0, 1)

@[simp] theorem enumerate_cap_zero (q : ℕ) (answer : List Bool → Bool) :
    enumerate q answer 0 = (0, 0) := by cases q <;> simp [enumerate]

/-- Exact count correctness and a safe explicit decision-call bound, including all zero cases. -/
theorem enumerate_spec {q : ℕ} {P : BitModels q → Prop} (D : ExactDecision P) (cap : ℕ) :
    (enumerate q D.answer cap).1 = min cap (modelCount P) ∧
      (enumerate q D.answer cap).2 ≤ 1 + 2 * q * min cap (modelCount P) := by
  induction q generalizing cap with
  | zero =>
    by_cases hc : cap = 0
    · subst cap; simp
    · have hbound := modelCount_bound P
      simp only [pow_zero] at hbound
      by_cases hd : D.answer [] = true
      · have hp := (modelCount_pos P).mpr (D.root.mp hd)
        simp only [enumerate, if_neg hc, if_pos hd]
        omega
      · have hz : modelCount P = 0 := by
          by_contra hn
          exact hd (D.root.mpr ((modelCount_pos P).mp (by omega)))
        simp [enumerate, hc, hd, hz]
  | succ q ih =>
    by_cases hc : cap = 0
    · subst cap; simp
    · by_cases hd : D.answer [] = true
      · have hl := ih (D.branch false) cap
        have hr := ih (D.branch true) (cap - (enumerate q (D.branch false).answer cap).1)
        have hp := (modelCount_pos P).mpr (D.root.mp hd)
        have hsplit := modelCount_branch P
        have hcount :
            (enumerate q (D.branch false).answer cap).1 +
              (enumerate q (D.branch true).answer
                (cap - (enumerate q (D.branch false).answer cap).1)).1 = min cap (modelCount P) := by
          omega
        simp only [enumerate, if_neg hc, if_pos hd]
        change _ = min cap (modelCount P) ∧ _ ≤ 1 + 2 * (q + 1) * min cap (modelCount P)
        refine ⟨hcount, ?_⟩
        have hpositive : 0 < min cap (modelCount P) := by omega
        have hlcall := hl.2
        have hrcall := hr.2
        rw [← hl.1] at hlcall
        rw [← hr.1] at hrcall
        change 1 + (enumerate q (D.branch false).answer cap).2 +
          (enumerate q (D.branch true).answer
            (cap - (enumerate q (D.branch false).answer cap).1)).2 ≤ _
        nlinarith
      · have hz : modelCount P = 0 := by
          by_contra hn
          exact hd (D.root.mpr ((modelCount_pos P).mp (by omega)))
        simp [enumerate, hc, hd, hz]

/-- Changing witness representation without changing existence does not change the count. -/
theorem modelCount_witness_invariant {q : ℕ} {W W' : Type*}
    (R : BitModels q → W → Prop) (R' : BitModels q → W' → Prop)
    (h : ∀ a, (∃ w, R a w) ↔ ∃ w', R' a w') :
    modelCount (fun a => ∃ w, R a w) = modelCount (fun a => ∃ w', R' a w') := by
  have he : (fun a => ∃ w, R a w) = (fun a => ∃ w', R' a w') := funext (fun a => propext (h a))
  rw [he]

theorem models_membership {q : ℕ} (S : Finset (BitModels q)) :
    models (fun a => a ∈ S) = S := by
  classical
  ext a
  simp [models]

theorem modelCount_membership {q : ℕ} (S : Finset (BitModels q)) :
    modelCount (fun a => a ∈ S) = S.card := by rw [modelCount, models_membership]

end PrefixEnumeration
end QecReliability
