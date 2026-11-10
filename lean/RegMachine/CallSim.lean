import RegMachine.CallMachine

/-!
# The oracle-call gadget: step-by-step simulation of the engine

`simA e o Mk s` is the abstract configuration of `callM` while simulating the engine
observation `o` (registers `s`): engine tape `e j` holds `eng (tape_j.nth (z - pos_j))
(z = 0)` on the *marked* cells `Mk j` and is blank elsewhere; its head is at the
engine's absolute head position. `SimInv o Mk`: the origin is marked, unmarked cells
of the engine tape are blank, and the engine's visited set is `Mk j` plus the head.

* `sim_step`: one engine step is exactly one gadget step (and marks the old cell);
* `sim_run`: an engine `Trace` is simulated with the same number of steps, inside any
  window containing the engine's final visited sets;
* `mark_step`: when the engine halts with `b`, one step marks the head cells and
  enters cleanup; afterwards the marked set is exactly the engine's visited set.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Engine tape contents: marked cells carry the engine symbol and the origin flag. -/
def engC (T : Tape ΓE) (p : ℤ) (Mk : Finset ℤ) : ℤ → Cell ΓE :=
  fun z => if z ∈ Mk then .eng (T.nth (z - p)) (decide (z = 0)) else .blank

theorem engC_step (T : Tape ΓE) (p : ℤ) (Mk : Finset ℤ) (h0 : (0 : ℤ) ∈ Mk) (x : ΓE) (m : Move) :
    update (engC T p Mk) p (.eng x (Cell.org (engC T p Mk p))) =
      engC (m.apply (T.write x)) (p + m.delta) (insert p Mk) := by
  funext z
  by_cases hz : z = p
  · subst hz
    rw [update_self]
    have hn : (m.apply (T.write x)).nth (z - (z + m.delta)) = x := by
      rw [nth_apply_write, if_pos (by ring)]
    have hl : engC (m.apply (T.write x)) (z + m.delta) (insert z Mk) z =
        .eng x (decide (z = 0)) := by
      simp only [engC, Finset.mem_insert_self, if_true, hn]
    rw [hl]
    congr 1
    by_cases hm : z ∈ Mk
    · simp only [engC, hm, if_true, Cell.org_eng]
    · have : z ≠ 0 := fun h => hm (h ▸ h0)
      simp only [engC, hm, if_false, Cell.org_blank, this, decide_false]
  · rw [update_of_ne hz]
    simp only [engC, Finset.mem_insert, hz, false_or, nth_apply_write]
    split_ifs with hm h1
    · omega
    · congr 2; ring
    · rfl

theorem engC_mark (T : Tape ΓE) (p : ℤ) (Mk : Finset ℤ) (h0 : (0 : ℤ) ∈ Mk)
    (hb : p ∉ Mk → T.nth 0 = default) :
    update (engC T p Mk) p (.eng (Cell.val (engC T p Mk p)) (Cell.org (engC T p Mk p))) =
      engC T p (insert p Mk) := by
  funext z
  by_cases hz : z = p
  · subst hz
    rw [update_self]
    by_cases hm : z ∈ Mk
    · simp [engC, hm]
    · have : z ≠ 0 := fun h => hm (h ▸ h0)
      simp [engC, hm, this, hb hm]
  · rw [update_of_ne hz]
    simp [engC, Finset.mem_insert, hz]

variable (E : Machine kE ΓE ΛE) (e : Embedding kE k) (q : Fin (k + 1))

/-- Abstract configuration of the gadget while simulating the engine observation `o`. -/
def simA (o : Observed kE ΓE ΛE) (Mk : Fin (kE + 1) → Finset ℤ) (s : Fin (k + 1) → List Bool) :
    ACfg k (Cell ΓE) (CallL kE ΛE) :=
  ⟨.sim o.core.label, assemble e (fun j => engC (o.core.tapes j) (o.position j) (Mk j)) (regC s),
    assemble e o.position (fun _ => 0)⟩

/-- Simulation invariant relating the marked sets to the engine observation. -/
structure SimInv (o : Observed kE ΓE ΛE) (Mk : Fin (kE + 1) → Finset ℤ) : Prop where
  zero_mem : ∀ j, (0 : ℤ) ∈ Mk j
  blank_out : ∀ j z, z ∉ Mk j → (o.core.tapes j).nth (z - o.position j) = default
  visited : ∀ j, o.visited j = insert (o.position j) (Mk j)

variable {E e}

theorem assemble_assemble {α : Type} (X Y : Fin (kE + 1) → α) (R : Fin (k + 1) → α) :
    assemble e X (assemble e Y R) = assemble e X R := by
  funext t
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht; simp
  · push_neg at ht
    rw [assemble_outside e _ _ ht, assemble_outside e _ _ ht, assemble_outside e _ _ ht]

theorem simA_val_heads {o : Observed kE ΓE ΛE} {Mk : Fin (kE + 1) → Finset ℤ}
    (h : SimInv o Mk) (s : Fin (k + 1) → List Bool) :
    (fun j => Cell.val ((simA e o Mk s).heads (e j))) = fun j => (o.core.tapes j).head := by
  funext j
  simp only [ACfg.heads, simA, assemble_image, engC]
  split_ifs with hm
  · simp
  · have := h.blank_out j (o.position j) hm
    simp only [sub_self, Tape.nth_zero] at this
    simp only [Cell.val_blank]
    exact this.symm

theorem sim_step {o o' : Observed kE ΓE ΛE} {Mk : Fin (kE + 1) → Finset ℤ} (h : SimInv o Mk)
    (hs : observedStep E o = some o') (s : Fin (k + 1) → List Bool) :
    SimInv o' (fun j => insert (o.position j) (Mk j)) ∧
      astep (callM E e q) (simA e o Mk s) =
        some (simA e o' (fun j => insert (o.position j) (Mk j)) s) := by
  unfold observedStep at hs
  cases ha : E.action o.core with
  | halt b => rw [ha] at hs; cases hs
  | advance l w mv =>
    rw [ha] at hs
    cases hs
    refine ⟨⟨fun j => Finset.mem_insert_of_mem (h.zero_mem j), ?_, fun j => ?_⟩, ?_⟩
    · intro j z hz
      simp only [Finset.mem_insert, not_or] at hz
      dsimp only
      rw [nth_apply_write, if_neg (by omega)]
      rw [show z - (o.position j + (mv j).delta) + (mv j).delta = z - o.position j by ring]
      exact h.blank_out j z hz.2
    · dsimp only
      rw [h.visited j]
    · have htr : (callM E e q).transition (simA e o Mk s).label (simA e o Mk s).heads =
          .advance (.sim l) (engWrite e (simA e o Mk s).heads (fun j x => .eng (w j) (Cell.org x)))
            (engMove e mv) := by
        apply callM_sim_advance
        rw [simA_val_heads h s]
        exact ha
      rw [astep_eng e htr]
      congr 1
      refine ACfg.ext rfl ?_ ?_
      · simp only [simA, assemble_image, assemble_assemble]
        congr 1
        funext j
        exact engC_step _ _ _ (h.zero_mem j) _ _
      · simp only [simA, assemble_image, assemble_assemble]

theorem inW_simA {o : Observed kE ΓE ΛE} {Mk : Fin (kE + 1) → Finset ℤ} (h : SimInv o Mk)
    (s : Fin (k + 1) → List Bool) {W : Fin (k + 1) → Set ℤ} (hW0 : ∀ t, (0 : ℤ) ∈ W t)
    (hsub : ∀ j, ↑(o.visited j) ⊆ W (e j)) : InW W (simA e o Mk s).P := by
  intro t
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht
    simp only [simA, assemble_image]
    apply hsub j
    rw [h.visited j]
    simp
  · push_neg at ht
    simp only [simA, assemble_outside e _ _ ht]
    exact hW0 t

theorem sim_run {o o' : Observed kE ΓE ΛE} {n : ℕ} (ht : Trace E o n o')
    (s : Fin (k + 1) → List Bool) {W : Fin (k + 1) → Set ℤ} (hW0 : ∀ t, (0 : ℤ) ∈ W t)
    (hsub : ∀ j, ↑(o'.visited j) ⊆ W (e j)) :
    ∀ Mk, SimInv o Mk → ∃ Mk', SimInv o' Mk' ∧
      ARun (callM E e q) W (simA e o Mk s) n (simA e o' Mk' s) := by
  induction ht with
  | nil o => exact fun Mk h => ⟨Mk, h, .nil (inW_simA h s hW0 hsub)⟩
  | @cons o o1 o2 n hs tail ih =>
    intro Mk h
    obtain ⟨h1, hst⟩ := sim_step (q := q) h hs s
    obtain ⟨Mk', h', hrun⟩ := ih hsub _ h1
    have hmono := (Trace.cons hs tail).visited_mono
    exact ⟨Mk', h', .cons hst (inW_simA h s hW0 fun j => (Finset.coe_subset.mpr (hmono j)).trans
      (hsub j)) hrun⟩

/-- Final engine contents: the whole visited set is marked. -/
def finC (o : Observed kE ΓE ΛE) : Fin (kE + 1) → ℤ → Cell ΓE :=
  fun j => engC (o.core.tapes j) (o.position j) (o.visited j)

theorem mark_step {o : Observed kE ΓE ΛE} {Mk : Fin (kE + 1) → Finset ℤ} (h : SimInv o Mk)
    {b : Bool} (hans : E.answer o.core = some b) (s : Fin (k + 1) → List Bool) :
    astep (callM E e q) (simA e o Mk s) =
      some ⟨.clean b 0 .right, assemble e (finC o) (regC s), assemble e o.position (fun _ => 0)⟩ := by
  have hact : E.action o.core = .halt b := by
    unfold Machine.answer at hans
    cases ha : E.action o.core with
    | halt c => rw [ha] at hans; cases hans; rfl
    | advance l w mv => rw [ha] at hans; cases hans
  have htr : (callM E e q).transition (simA e o Mk s).label (simA e o Mk s).heads =
      .advance (.clean b 0 .right)
        (engWrite e (simA e o Mk s).heads (fun _ x => .eng (Cell.val x) (Cell.org x)))
        (engMove e (fun _ => .stay)) := by
    apply callM_sim_halt
    rw [simA_val_heads h s]
    exact hact
  rw [astep_eng e htr]
  congr 1
  refine ACfg.ext rfl ?_ ?_
  · simp only [simA, assemble_image, assemble_assemble]
    congr 1
    funext j
    rw [finC, h.visited j]
    refine engC_mark _ _ _ (h.zero_mem j) fun hm => ?_
    have := h.blank_out j (o.position j) hm
    simpa using this
  · simp only [simA, assemble_image, assemble_assemble, Move.delta, add_zero]

end QecReliability.RegMachine
