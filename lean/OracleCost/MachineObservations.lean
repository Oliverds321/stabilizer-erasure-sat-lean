import OracleCost.MultiTape
import Mathlib.Tactic.Linarith

/-! Lift finite core runs to ghost position/visited-cell observations. The
linear-in-time space bound is useful for short wrapper primitives; it is not
substituted for the external SAT machine's independent polynomial space bound.
-/
namespace QecReliability.OracleCost.MultiTape
variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

theorem observedStep_exists {M : Machine k Γ Λ} {s : Observed k Γ Λ}
    {t : Config k Γ Λ} (h : M.step s.core=some t) :
    ∃ u, observedStep M s=some u ∧ u.core=t := by
  cases ha : M.action s.core with
  | halt b => simp [Machine.step,ha] at h
  | advance label write move =>
    simp only [Machine.step,ha,Option.some.injEq] at h
    subst t
    refine ⟨⟨⟨label,fun i => (move i).apply ((s.core.tapes i).write (write i))⟩,
      fun i => s.position i+(move i).delta,
      fun i => insert (s.position i+(move i).delta) (s.visited i)⟩,?_,rfl⟩
    simp [observedStep,ha]

theorem CoreTrace.observe {M : Machine k Γ Λ} {s t : Config k Γ Λ} {n : ℕ}
    (h : CoreTrace M s n t) (initial : Observed k Γ Λ) (hi : initial.core=s) :
    ∃ final, Trace M initial n final ∧ final.core=t := by
  induction h generalizing initial with
  | nil s => exact ⟨initial,.nil _,hi⟩
  | cons he tail ih =>
    obtain ⟨next,hs,hn⟩ := observedStep_exists (hi ▸ he)
    obtain ⟨final,ht,hf⟩ := ih next hn
    exact ⟨final,.cons hs ht,hf⟩

theorem observedStep_cells {M : Machine k Γ Λ} {s t : Observed k Γ Λ}
    (h : observedStep M s=some t) : visitedCells t≤visitedCells s+(k+1) := by
  cases ha : M.action s.core with
  | halt b => simp [observedStep,ha] at h
  | advance label write move =>
    simp only [observedStep,ha,Option.some.injEq] at h
    subst t
    calc
      _ ≤ ∑ i : Fin (k+1), ((s.visited i).card+1) :=
        Finset.sum_le_sum (fun i _ => Finset.card_insert_le _ _)
      _ = _ := by simp [Finset.sum_add_distrib,visitedCells]

theorem Trace.space_le {M : Machine k Γ Λ} {s t : Observed k Γ Λ} {n : ℕ}
    (h : Trace M s n t) : visitedCells t≤visitedCells s+(k+1)*n := by
  induction h with
  | nil => simp
  | cons he tail ih =>
    have hs := observedStep_cells he
    nlinarith

theorem initialObserved_cells (M : Machine k Γ Λ) (bits : List Bool) :
    visitedCells (initialObserved M bits)≤(k+1)*(bits.length+1) := by
  calc
    _ ≤ ∑ _i : Fin (k+1), (bits.length+1) := by
      unfold visitedCells
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i=0
      · simp only [initialObserved,hi,↓reduceIte]
        exact (Finset.card_insert_le _ _).trans (by
          have hc := Finset.card_image_le (s:=Finset.range bits.length) (f:=fun j : ℕ => (j:ℤ))
          simpa only [Finset.card_range] using Nat.add_le_add_right hc 1)
      · simp only [initialObserved,hi,↓reduceIte,Finset.card_singleton]
        omega
    _ = _ := by simp

/-- Every halting core trace produces a completed observed run with the same
time and core result. This statement uses no unproved termination assumption. -/
theorem completed_of_core {M : Machine k Γ Λ} {bits : List Bool}
    {n : ℕ} {final : Config k Γ Λ} {answer : Bool}
    (h : CoreTrace M (M.initial bits) n final) (ha : M.answer final=some answer) :
    ∃ run : Completed M bits, run.final.core=final ∧ run.time=n+1 ∧
      run.cells≤(k+1)*(bits.length+n+1) := by
  obtain ⟨last,ht,hf⟩ := h.observe (initialObserved M bits) rfl
  refine ⟨⟨n,last,answer,ht,by rwa [hf]⟩,hf,rfl,?_⟩
  have hc := ht.space_le
  have hi := initialObserved_cells M bits
  change visitedCells last≤_
  nlinarith

end QecReliability.OracleCost.MultiTape
