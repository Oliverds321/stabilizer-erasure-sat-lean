import TensorRepairFLWrapper
import TensorRepairFLTableBounds

/-! Binary count-table conversion bounds for the actual FL callback. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (wi : WrapperIndices)

def CountListBound (B : ℕ) (xs : List RawRatio) : Prop := ∀ x ∈ xs, RB B x

theorem headCount_bits {B : ℕ} {xs : List RawRatio} (h : CountListBound B xs) :
    (xs.headD (0,0)).1.size ≤ B := by
  cases xs with
  | nil => simp only [List.headD_nil,Prod.fst,Nat.size_zero]; exact Nat.zero_le _
  | cons x xs => exact (h x (by simp)).1

theorem countList_tail {B : ℕ} {xs : List RawRatio} (h : CountListBound B xs) :
    CountListBound B xs.tail := by
  intro x hx
  exact h x (List.mem_of_mem_tail hx)

theorem rawCounts_bits {B : ℕ} {a b : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B) :
    RB (2*B+1) (countsR a b) := by
  apply countsR_RB (by omega)
  have hs := NatSize.size_add_le' a b
  omega

theorem countDataR_bound (D B : ℕ) (keys : List Key) (gs bs : List RawRatio)
    (hk : ∀ key ∈ keys, mag TKey key ≤ D)
    (hg : CountListBound B gs) (hb : CountListBound B bs) :
    TableBound D (2*B+1) (countDataR keys gs bs) := by
  induction keys generalizing gs bs with
  | nil => intro x hx; simp [countDataR] at hx
  | cons key keys ih =>
    have ht := ih gs.tail bs.tail (fun key h => hk key (by simp [h]))
      (countList_tail hg) (countList_tail hb)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hk key (by simp),rawCounts_bits (headCount_bits hg) (headCount_bits hb)⟩
    · exact ht x hx

def countStepBudget (D B N : ℕ) : ℕ := 1000*(D+B+1)*(N+1)

/-- A proof-only expanded view of the unchanged body, exposing private list
projections to resource simplification in downstream modules. -/
@[tm_simp] def countsStepExpanded : Tm [.prod TCountState TKey] TCountState :=
  .pair (.lcase (.fst (.fst Tm.v0)) .lnil Tm.v1)
    (.pair (.lcase (.fst (.snd (.fst Tm.v0))) .lnil Tm.v1)
      (.lcons (.pair (.snd Tm.v0) (.app (countsF wi.countsRatio)
        (.pair (.lcase (.fst (.fst Tm.v0)) .zero (.fst Tm.v0))
          (.lcase (.fst (.snd (.fst Tm.v0))) .zero (.fst Tm.v0)))))
        (.snd (.snd (.fst Tm.v0)))))

@[tm_simp] theorem countsStepBody_expanded : countsStepBody wi = countsStepExpanded wi := rfl

@[tm_simp] theorem countsStepF_expanded : countsStepF wi =
    Trans.Control.bodySig wi.countsStep (countsStepExpanded wi) := rfl

/-- Exact costs of one count conversion, before list allocation bounds. -/
theorem countsStep_cost (gs bs : List RawRatio) (acc : RawTable) (key : Key) :
    (countsStepF wi).cost ((gs,bs,acc),key) ≤
      (countsF wi.countsRatio).cost ((gs.headD (0,0)).1,(bs.headD (0,0)).1)+40 := by
  cases gs <;> cases bs <;>
    simp only [countsStepF_expanded,bodySig_cost,countsStepExpanded,tm_simp,List.headD_nil,List.headD_cons]
  all_goals norm_num only [Nat.reduceAdd]
  all_goals omega

theorem countsStep_depth (gs bs : List RawRatio) (acc : RawTable) (key : Key) :
    (countsStepF wi).depth ((gs,bs,acc),key) ≤
      (countsF wi.countsRatio).depth ((gs.headD (0,0)).1,(bs.headD (0,0)).1)+1 := by
  cases gs <;> cases bs <;>
    simp only [countsStepF_expanded,bodySig_depth,countsStepExpanded,tm_simp,List.headD_nil,List.headD_cons]
  all_goals omega

end QecReliability.TensorMachine.RepairFL
